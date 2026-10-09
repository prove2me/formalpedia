-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineLength_ready
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineLength_ready
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T11:51:37.010978+00:00
-- url     : https://prove2.me/theorems/6ccfd4cc-ba54-4b06-b8d8-fc601abdc9b9
-- title:
--   A sampler scale above the allocated affine length budget meets three scale requirements
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ for $j \in \mathrm{Fin}\,m$; finite types $B_a$ indexed by the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \sqcup \mathrm{Fin}\,n_j$); a finite type $\alpha$; finite types $O_j$; finite types $J_j$ with real subspaces $U_j \subseteq \mathbb R^{J_j}$; for each $j$ a basis `basis j`, indexed by $\mathrm{Fin}\,n_j$, of the orthogonal complement of `euclideanSubspace (U j)` (the Euclidean copy of $U_j$); and real functions $R, \sigma$ on $\mathrm{Fin}\,m$. Let $D, P, P_\rho, P_k, \mathrm{target}, F, T$ be real numbers. Assume `AllocatedComparisonDimensions B α O D` (a structure stating that $D \ge 0$ bounds $m$, $|G|$, $|\alpha|$ and a list of further cardinalities and constants built from the data), that $P, P_\rho, P_k, \mathrm{target}, F, T \ge 0$, and let `S : LayerSamplerScale B U basis R σ` be a layer-sampler scale (a structure bundling a positive natural number `S.value` with width and gap inequalities) with
--   $$\exp(\texttt{allocatedAffineLengthLog}\ m\ D\ P\ P_\rho\ P_k\ \mathrm{target}\ F\ T) \le S.\mathrm{value}.$$
--   Write $e = $ `allocatedAffineCoefficientAccuracyLog m D P Prho Pk target` and $E = $ `allocatedAffineReferenceAccuracyLog m D P Prho Pk target` (explicit real expressions defined by OpenAI). Then all three hold: $\exp(\texttt{allocatedKernelReplacementLog}\ B\ \alpha\ O\ P\ e) \le S.\mathrm{value}$; $1/S.\mathrm{value}^{\,\texttt{layerTailDegree}\ m + 1} \le e^{-E}$, where `layerTailDegree m` $= m\,(2^{m+1}+1)$; and $\exp(\texttt{progressionSliceLengthLog}\ D\ E\ F\ T) \le S.\mathrm{value}$, where `progressionSliceLengthLog D E F T` $= E + F + T + D + {}$`scalarCubeRiemannLog D` $+\,5$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineLength_ready` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineScaleEnvelope.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B129` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineScaleEnvelope.lean#L377

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B129

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

 theorem allocatedAffineLength_ready {D P Prho Pk target F T : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk) (ht : 0 ≤ target)
    (hF : 0 ≤ F) (hT : 0 ≤ T)
    (S : LayerSamplerScale (G := G) B U basis R σ)
    (hS : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F T) ≤ S.value) :
    let e := allocatedAffineCoefficientAccuracyLog m D P Prho Pk target
    let E := allocatedAffineReferenceAccuracyLog m D P Prho Pk target
    Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value ∧
      1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp (-E) ∧
      Real.exp (progressionSliceLengthLog D E F T) ≤ S.value := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
