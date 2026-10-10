-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineLength_slice_ready
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineLength_slice_ready
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T13:18:26.583509+00:00
-- url     : https://prove2.me/theorems/07accdf6-315b-40f2-91aa-46dbb1d9c771
-- title:
--   Long progression slices on the non-grid principal tuples meet the slice requirements
-- statement:
--   Fix the section data $m$, $G$, $I$, $n$, $B$, $\alpha$ (now with decidable equality), $O$, $J$, $U$, `basis`, $R$, $\sigma$ as in `allocatedAffineLength_ready` (finite types $G$, $I_j$, $B_a$ over the axes $a$ of `LayerSamplerAxis I n`, $\alpha$, $O_j$, $J_j$; subspaces $U_j \subseteq \mathbb R^{J_j}$; bases `basis j` of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$). Let $D, P, P_\rho, P_k, \mathrm{target}, F, T, \delta$ be real numbers with `AllocatedComparisonDimensions B α O D` and $P, P_\rho, P_k, \mathrm{target}, F, T \ge 0$, and let `S : LayerSamplerScale B U basis R σ` satisfy $\exp(\texttt{allocatedAffineLengthLog}\ m\ D\ P\ P_\rho\ P_k\ \mathrm{target}\ F\ T) \le S.\mathrm{value}$. Let $H, \mathrm{step}$ be natural-valued and $c$ integer-valued functions on the principal tuple index `PrincipalTupleIndex B (layerSamplerDegree I n)` (the sigma type of triples $(a, b, i)$ with $b \in B_a$ and $i < $ `layerSamplerDegree I n a`), such that for every $j$ the progression $\{c_j + \mathrm{step}_j\,k : 0 \le k < H_j\}$ (`integerProgressionSupport (c j) (step j) (H j)`) lies in $[0, \texttt{allocatedPrincipalSides B U basis S j})$, the latter being a natural-number side length defined by OpenAI. Assume $0 < \delta$, $\delta^{-1} \le e^{F}$, and let $\mathrm{modulus}$ be a natural number with $0 < \mathrm{modulus} \le e^{T}$. Let $\mathrm{grid}$ be the predicate `allocatedGridAxis U basis S.value` on axes, let $\mathrm{Tuple}$ be the principal tuple index restricted to axes $a$ with $\neg\,\mathrm{grid}\,a$, embedded into the full index, and $E = $ `allocatedAffineReferenceAccuracyLog m D P Prho Pk target`. Then: if $0 < \mathrm{step}_j$ for every $j \in \mathrm{Tuple}$, and $\delta \cdot \texttt{allocatedPrincipalSides}_j \le |\texttt{integerProgressionSupport}(c_j, \mathrm{step}_j, H_j)|$ for every $j \in \mathrm{Tuple}$, then for all $j \in \mathrm{Tuple}$: $2 \le H_j$; $(|\alpha|+1)\,\mathrm{modulus} \le H_j$; `scalarCubeGridBoundaryConstant α` $\cdot\, \mathrm{modulus}/H_j$ is strictly less than the Lebesgue measure of `scalarCubeDomain α` (a subset of $\mathbb R^{\mathrm{Option}\,\alpha}$ defined by OpenAI); and further $\sum_{j \in \mathrm{Tuple}} \mathrm{modulus}/H_j \le e^{-E}$, and $\mathrm{step}_j / \texttt{allocatedPrincipalSides}_j \le e^{-E}$ for all $j \in \mathrm{Tuple}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineLength_slice_ready` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineScaleEnvelope.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B129`, `OAIErdos3B133` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineScaleEnvelope.lean#L409

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B129
import Definitions.Def_OAIErdos3B133

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

 theorem allocatedAffineLength_slice_ready [DecidableEq α]
    {D P Prho Pk target F T δ : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk) (ht : 0 ≤ target)
    (hF : 0 ≤ F) (hT : 0 ≤ T)
    (S : LayerSamplerScale (G := G) B U basis R σ)
    (hS : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F T) ≤ S.value)
    (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
    (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S j : ℤ))
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (modulus : ℕ) (hm : 0 < modulus) (hmT : (modulus : ℝ) ≤ Real.exp T) :
    let grid := allocatedGridAxis (I := I) U basis S.value
    let Tuple := PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    let embed := fun j : Tuple => (⟨j.1.val, j.2⟩ : PrincipalTupleIndex B (layerSamplerDegree I n))
    let E := allocatedAffineReferenceAccuracyLog m D P Prho Pk target
    (∀ j : Tuple, 0 < step (embed j)) →
    (∀ j : Tuple, δ * allocatedPrincipalSides B U basis S (embed j) ≤
      ((integerProgressionSupport (c (embed j)) (step (embed j) : ℤ) (H (embed j))).card : ℝ)) →
    (∀ j : Tuple, 2 ≤ H (embed j)) ∧
    (∀ j : Tuple, (Fintype.card α + 1) * modulus ≤ H (embed j)) ∧
    (∀ j : Tuple, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H (embed j)) <
      MeasureTheory.volume.real (scalarCubeDomain α)) ∧
    (∑ j : Tuple, (modulus : ℝ) / H (embed j)) ≤ Real.exp (-E) ∧
    (∀ j : Tuple, (step (embed j) : ℝ) / allocatedPrincipalSides B U basis S (embed j) ≤
      Real.exp (-E)) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
