-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPathSlicedPerturbation_chosen_tail_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFixedPathSlicedPerturbation_chosen_tail_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:34:49.309225+00:00
-- url     : https://prove2.me/theorems/2d7ca0d6-1e28-4cb8-8e74-ab94a6e9ac24
-- title:
--   A single explicit perturbation size works for the sliced principal C2 tolerance of every layer sampler scale
-- statement:
--   Let $m$ be a natural number and $G$ a finite type. For each $j < m$ let $I_j$ and $J_j$ be finite types, $n_j$ a natural number, $U_j$ a real subspace of $\mathbb{R}^{J_j}$ and $\mathrm{basis}_j$ a real basis, indexed by $\{0, \dots, n_j - 1\}$, of the orthogonal complement of the Euclidean subspace given by $U_j$. The layer sampler axes (OpenAI's `LayerSamplerAxis I n`) are the pairs $(j, c)$ with $j < m$ and $c \in I_j \sqcup \{0, \dots, n_j - 1\}$; for each axis $a$ let $B_a$ be a finite type. The axis $(j, c)$ has degree $j + 1$ (OpenAI's `layerSamplerDegree I n`), and OpenAI's index type `PrincipalTupleIndex B (layerSamplerDegree I n)` consists of the triples $(a, b, r)$ with $a$ an axis, $b \in B_a$ and $r < \deg a$.
--
--   Let $D, P, \mathrm{cost}, E, \eta$ be real numbers with $D, P, \mathrm{cost}, E \ge 0$, assume the number of elements of `PrincipalTupleIndex B (layerSamplerDegree I n)` is at most $D$ and the number of layer sampler axes is at most $D$, and let $A \ge 0$ be a real number with $0 < \eta$, $A \le e^{P}$ and $\eta^{-1} \le e^{E}$. Let
--   $$Q_\sigma = \texttt{fixedPathSlicedPerturbationLog}\ D\ (D + P + 4)\ (\mathrm{cost} + 1)\ E\ m$$
--   (an explicit real quantity defined by OpenAI) and $t = e^{-Q_\sigma}$. Then $0 < t$, $t \le 1$, and for all $R, \sigma : \{0,\dots,m-1\} \to \mathbb{R}$ and every layer sampler scale $S$ (an OpenAI `LayerSamplerScale B U basis R σ`, a structure whose main field is a positive natural number `S.value`, subject to width and gap conditions) the following holds. Let the active axes be those $a$ for which `allocatedShortAxis U basis S.value a` fails, where `allocatedShortAxis U basis ℓ (j, c)` (OpenAI) is false when $c \in I_j$ and, when $c$ is an index $i < n_j$, says that `basisAxisScale (basis j) i` $\le \ell^{j+1}$, with `basisAxisScale b i` $= \lceil 1/\lVert b_i \rVert \rceil$ (natural-number ceiling, OpenAI). Let $\mathrm{inputs}$ be the triples $(a, b, r)$ with $a$ an active axis, $b \in B_a$ and $r < \deg a$, with $|\mathrm{inputs}|$ elements, and let $|\mathrm{active}|$ be the number of active axes. Then
--   $$|t| \cdot \texttt{polynomialMassC2Budget}\ |\mathrm{inputs}|\ m\ 1 \le \texttt{slicedPrincipalC2Tolerance}\ |\mathrm{inputs}|\ |\mathrm{active}|\ m\ 1\ \bigl(\texttt{unitProfilePrincipalLowerBound}\ B\bigr)\ \bigl(e^{-\mathrm{cost}}/2\bigr)\ A\ \eta,$$
--   where `polynomialMassC2Budget N d C` $= (1 + N d)^2\, C$, `unitProfilePrincipalLowerBound B` $= 1/\bigl(8(\sum_a |B_a| + 1)\bigr)$, and `slicedPrincipalC2Tolerance` is an explicit real quantity, all defined by OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFixedPathSlicedPerturbation_chosen_tail_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedFixedPathSlicedPerturbation_chosen_tail` (in `lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedSourceErrorBudget.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B067`, `OAIE3v2B105` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedSourceErrorBudget.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedFixedPathSlicedPerturbation_chosen_tail)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B067
import Definitions.Def_OAIE3v2B105

section

namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal Classical

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem allocatedFixedPathSlicedPerturbation_chosen_tail_s2
    {D P cost E η : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hcost : 0 ≤ cost) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (A : ℝ≥0) (hη : 0 < η) (hAP : (A : ℝ) ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E) :
    let Qσ := fixedPathSlicedPerturbationLog D (D + P + 4) (cost + 1) E m
    let t := Real.exp (-Qσ)
    0 < t ∧ t ≤ 1 ∧ ∀ {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ),
    let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
    let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    |t| * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
        m 1 (unitProfilePrincipalLowerBound B) (Real.exp (-cost) / 2) A η := by
  sorry

end VectorPolynomial
end Erdos3

end

end OAI
end
