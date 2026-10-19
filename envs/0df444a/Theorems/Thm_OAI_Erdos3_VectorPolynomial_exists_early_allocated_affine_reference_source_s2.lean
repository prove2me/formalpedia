-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_early_allocated_affine_reference_source_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_reference_source_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:48:22.520796+00:00
-- url     : https://prove2.me/theorems/c101a64c-e4c0-44e5-ae4c-a99446f4f8d8
-- title:
--   Existence of radii and a tolerance for which the allocated affine reference comparison holds
-- statement:
--   Let $m$ be a natural number and $G$ a finite type with decidable equality. For $j \in \operatorname{Fin} m$ let $I_j$ be a finite type and $n_j$ a natural number; let $B$ assign a finite type with decidable equality to each element of `LayerSamplerAxis I n` (pairs $(j, a)$ with $a \in I_j \sqcup \operatorname{Fin} n_j$). Let $\alpha$ be a finite type with decidable equality, and for each $j$ let $O_j$ be a finite nonempty type with decidable equality. Let `rows j` $: O_j \to$ finite subsets of $\alpha$ be injective for every $j$, with $|\texttt{rows } j\ o| \le j + 1$ for all $j$ and $o$.
--
--   Let $\psi : \mathbb{R} \to \mathbb{R}$ be infinitely differentiable with $\psi(t) \in [0, 1]$ for all $t$, $\psi(t) = 0$ when $|t| \le 1$, and $\psi(t) = 1$ when $|t| \ge 2$. Let $A, T \in \mathbb{R}_{\ge 0}$ with $\psi$ $A$-Lipschitz and Mathlib's `Real.smoothTransition` $T$-Lipschitz. Let `block a` $: O_{j(a)} \to B(a)$ be an injective map for every axis $a$ (where $j(a)$ is the layer of $a$). Let $\delta, \eta$ be reals with $0 < \delta \le 1$ and $\eta > 0$.
--
--   Then there exist $\rho_{\min} \in \mathbb{R}_{\ge 0}$ with $\rho_{\min} > 0$ and a function $\rho$ from predicates $P$ on axes to $\mathbb{R}_{\ge 0}$ such that, for every $P$, $\rho_{\min} \le \rho(P) \le 1$ and
--   $\rho(P) =$ `partitionedAffineSourceRadius (layerSamplerDegree I n) P A T (δ / 2) η`
--   (an explicit radius defined by OpenAI, computed for the axes not satisfying $P$ with output types $O_{j(a)}$); and there exists a real $t$ with $0 < t \le 1$,
--   $t =$ `allocatedAffineSourceTolerance B A T (δ / 2) η`
--   (OpenAI's tolerance: the minimum over all predicates $P$ of `partitionedAffineSourceTolerance`), and `AllocatedAffineReferenceComparison B rows δ η ρ t`. The last is OpenAI's predicate: for all families $J$, subspaces $U$, bases, positive $R, \sigma$ with $\sigma_j \le t$ and every `LayerSamplerScale` (and the further data quantified in its definition), the $L^1$ distance, against OpenAI's long jet reference measure, between the long profile density of the ideal profile and that of the discrete profile is at most `allocatedAffineSourceReferenceError` with radius $\rho(\texttt{allocatedGridAxis U basis S.value})$. (The universe level of $J$ in that predicate is a fixed universe `uJ`.)
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_reference_source_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_reference_source` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineWholeProfileComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B213` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineWholeProfileComparison.lean (declaration OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_reference_source)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B213

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_affine_reference_source_s2
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T (δ / 2) η) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T (δ / 2) η ∧
      AllocatedAffineReferenceComparison.{uJ, _, _, _, _, _} (G := G) B rows δ η ρ t := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
