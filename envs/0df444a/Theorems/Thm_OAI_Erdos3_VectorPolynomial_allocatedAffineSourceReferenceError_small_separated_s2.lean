-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineSourceReferenceError_small_separated_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineSourceReferenceError_small_separated_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:39:43.724835+00:00
-- url     : https://prove2.me/theorems/53bf473b-75ca-48f7-acc9-5dd6836ae7c4
-- title:
--   The allocated affine source-reference error is at most exp(-target) under separated smallness conditions
-- statement:
--   Let $m$ be a natural number and $G$ a finite type. For $j \in \operatorname{Fin} m$ let $I_j$, $J_j$, $O_j$ be finite types and $n_j$ a natural number; let $B$ assign a finite type to each element of `LayerSamplerAxis I n` (pairs $(j, a)$ with $a \in I_j \sqcup \operatorname{Fin} n_j$). For each $j$ let $U_j$ be a real subspace of $J_j \to \mathbb{R}$ and `basis j` a real basis, indexed by $\operatorname{Fin} n_j$, of the orthogonal complement of `euclideanSubspace (U j)` (that subspace inside the Euclidean space $\mathbb{R}^{J_j}$; defined by OpenAI). Let $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ and let $S$ be a `LayerSamplerScale B U basis R σ` (OpenAI's structure containing a positive natural number `S.value`). Let $\alpha$ be a finite type with decidable equality.
--
--   Write `grid` for the predicate `allocatedGridAxis U basis S.value` on axes (defined by OpenAI: an integer axis $(j, i)$ is a grid axis when its basis scale is at most $\texttt{S.value}^{\texttt{layerTailDegree } m + 1}$; real axes are not). Let `Outputs` be the type of pairs $(a, o)$ with $a$ a non-grid axis in layer $j$ and $o \in O_j$; call such a pair an integer output if $a$ is an integer axis (`allocatedLongIntegerCoordinate`), and let `select` (`allocatedLongIntegerSelect`) be the inclusion of integer outputs into `Outputs`, so that `UnselectedColumn select` is the set of outputs not in its range.
--
--   Let $\rho \in \mathbb{R}_{\ge 0}$ and $P \in \mathbb{R}$, let $M, H$ be natural-number-valued functions on `PrincipalTupleIndex` for the non-grid axes (pairs (non-grid axis $a$, element of $B(a) \times \operatorname{Fin}(\text{degree of } a)$), where the degree of an axis of layer $j$ is $j+1$), and let $D, L, \mathrm{target}, \eta, \varepsilon, \mathrm{mesh}, C_{\mathrm{mask}}, \mathrm{earlyMaskLog}$ be reals. Assume:
--
--   - $C_{\mathrm{mask}}^{K} \le e^{\mathrm{earlyMaskLog}}$, where $K$ is the number of elements of `LayerSamplerAxis I n`;
--   - $D \ge 0$, $L \ge 0$, $P \le L$;
--   - `allocatedDensityLog B α O P` $\le L$ and `allocatedJetSupportLog B α O P` $\le L$ (explicit real functions of OpenAI);
--   - `partitionedIdealRadius α m` $+ 1 \le e^L$, where `partitionedIdealRadius α m` $= 1/4 + 2^{|\alpha|}(|\alpha| + 1)^m$;
--   - $\bigl(\prod_{(a, o) \in \texttt{Outputs}} |R_{j(a)}|\bigr)^{-1} \cdot \texttt{affineProductProfileLip Outputs } \rho \cdot e^P \le e^L$, where $j(a)$ is the layer of $a$ and `affineProductProfileLip Outputs ρ` $= |\texttt{Outputs}| \cdot$ `probabilityProfileLipschitz` $\cdot \rho^{-(|\texttt{Outputs}|+1)}$ (OpenAI's constants);
--   - $0 \le C_{\mathrm{mask}} \le e^L$;
--   - $0 \le c_\alpha / \operatorname{vol}(\texttt{scalarCubeDomain } \alpha) \le e^L$, where $c_\alpha$ = `scalarCubeGridBoundaryConstant α` (an explicit constant of OpenAI) and `scalarCubeDomain α` is the set of $a : \mathrm{Option}\ \alpha \to \mathbb{R}$ all of whose scalar cube values lie in $(0, 1)$, with Lebesgue volume;
--   - $K \le D$, $|\texttt{Outputs}| \le D$, $|\texttt{UnselectedColumn select}| \le D$, and the number of integer outputs is $\le D$;
--   - $\eta \ge 0$, $\varepsilon \ge 0$, $\mathrm{mesh} \ge 0$, and $\eta \le e^{-(\mathrm{target} + \mathrm{earlyMaskLog} + 4)}$;
--   - with $A$ = `affineReferenceCoefficientLog D L` $= 8(D+1)(L+1)$: $\sum_j M_j / H_j \le e^{-(\mathrm{target} + A + 4)}$, $\varepsilon \le e^{-(\mathrm{target} + A + 4)}$ and $\mathrm{mesh} \le e^{-(\mathrm{target} + A + 4)}$.
--
--   Then `allocatedAffineSourceReferenceError B U basis S α O ρ P η M H ε mesh Cmask` $\le e^{-\mathrm{target}}$, where `allocatedAffineSourceReferenceError` is OpenAI's explicit real-valued error term built from these parameters.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineSourceReferenceError_small_separated_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedAffineSourceReferenceError_small_separated` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineWholeProfileComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B213` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineWholeProfileComparison.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedAffineSourceReferenceError_small_separated)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B213

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (α : Type*) [Fintype α] [DecidableEq α] (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "Outputs" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "select" => allocatedLongIntegerSelect B U basis S (O := O)

theorem allocatedAffineSourceReferenceError_small_separated_s2
    (ρ : ℝ≥0) (P : ℝ)
    (M H : PrincipalTupleIndex
      (fun a : {a // ¬grid a} => B a.val)
      (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val) → ℕ)
    {D L target η ε mesh Cmask earlyMaskLog : ℝ}
    (hearlyMask : Cmask ^ Fintype.card (LayerSamplerAxis I n) ≤ Real.exp earlyMaskLog)
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hP : P ≤ L)
    (hdensity : allocatedDensityLog (G := G) B α O P ≤ L)
    (hsupport : allocatedJetSupportLog (G := G) B α O P ≤ L)
    (hideal : partitionedIdealRadius α m + 1 ≤ Real.exp L)
    (hKi : ‖(∏ o : Outputs, |R o.1.val.1|)⁻¹‖ *
      ((affineProductProfileLip Outputs ρ : ℝ) * Real.exp P) ≤ Real.exp L)
    (hCmask0 : 0 ≤ Cmask) (hCmask : Cmask ≤ Real.exp L)
    (hb0 : 0 ≤ scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α))
    (hb : scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) ≤ Real.exp L)
    (ha : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (ho : (Fintype.card Outputs : ℝ) ≤ D)
    (hu : (Fintype.card (UnselectedColumn select) : ℝ) ≤ D)
    (hi : (Fintype.card {o : Outputs // allocatedLongIntegerCoordinate B U basis S (O := O) o} : ℝ) ≤ D)
    (hη0 : 0 ≤ η) (hε0 : 0 ≤ ε) (hmesh0 : 0 ≤ mesh)
    (hη : η ≤ Real.exp (-(target + earlyMaskLog + 4)))
    (hratio : (∑ j, (M j : ℝ) / H j) ≤ Real.exp (-(target + affineReferenceCoefficientLog D L + 4)))
    (hε : ε ≤ Real.exp (-(target + affineReferenceCoefficientLog D L + 4)))
    (hmesh : mesh ≤ Real.exp (-(target + affineReferenceCoefficientLog D L + 4))) :
    allocatedAffineSourceReferenceError B U basis S α O ρ P η M H ε mesh Cmask ≤ Real.exp (-target) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
