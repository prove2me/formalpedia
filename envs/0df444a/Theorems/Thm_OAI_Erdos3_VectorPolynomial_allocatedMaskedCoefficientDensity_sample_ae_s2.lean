-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedMaskedCoefficientDensity_sample_ae_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedMaskedCoefficientDensity_sample_ae_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:44:03.343795+00:00
-- url     : https://prove2.me/theorems/5465b2ae-cd9c-439f-9cd6-4aaacc408f9e
-- title:
--   Almost surely, the masked coefficient density at a canonical deck sample equals the test value times the coefficient density
-- statement:
--   Fix the data of OpenAI's allocated layer-sampler setup: a natural number $m$; finite types $G$, $I_j$, $J_j$ (with decidable equality) and $E_j$ for $j < m$, and $B(a)$ for each layer-sampler axis $a$; dimensions $n_j$; subspaces $U_j \subseteq \mathbb{R}^{J_j}$; $\mathbb{Z}$-bases $bW_j$ (indexed by $E_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; bases $b_j$ (indexed by $\{0, \dots, n_j - 1\}$) of the orthogonal complement of $U_j$ with $hb$: the $\mathbb{Z}$-span of $b_j$ equals `projectedIntegerLattice (euclideanSubspace (U j))`; orthonormal bases $o_j$ (indexed by $I_j$) of $U_j$; real vectors $R, \sigma$ indexed by $j < m$; and a `LayerSamplerScale B U b R σ` $S$ (all defined by OpenAI).
--
--   Assume $R_j > 0$ and $0 < \sigma_j \le 1$ for all $j$, and let $C_j \ge 0$ be reals with $\lVert \texttt{normalizedOrthogonalChart}(U_j, b_j)^{-1}(v)\rVert \le C_j \lVert v\rVert$ for all $j$ and $v$, and $C_j (\lvert I_j\rvert + 1) R_j \le 1/4$ for all $j$. Let $q \ge 1$ be a natural number and let `test` be any real-valued function on `CoefficientChartResidues (LayerSamplerVariables G I n B) n E q` (the chart residues modulo $q$).
--
--   Then for almost every $z = (z_1, z_2)$ with respect to the product of the probability measure `allocatedCoefficientSource B U b hR hσ S` (OpenAI's source law on coefficient samples) and the uniform probability measure on the finite set `CoefficientDeckResidues (LayerSamplerVariables G I n B) E q`, writing $y$ = `canonicalCoefficientDeckSample U bW b hb o q z₁ z₂`,
--   $$\texttt{allocatedMaskedCoefficientDensity B U b o S q}\bigl(\texttt{coefficientDeckResidueMask U bW b hb q test}\bigr)(y) = \texttt{test}\bigl(\texttt{coefficientSamplerChartResidues q z1 z2}\bigr) \cdot \texttt{allocatedCoefficientDensity B U b hb o hR hsigma S}\bigl(\texttt{quotientIntegerCover (coefficientIntegerLattice U) q}\ y\bigr).$$
--   Here `allocatedCoefficientDensity` is OpenAI's density of the coefficient source on the coefficient torus, `quotientIntegerCover … q` is the projection from the $q$-fold cover to the torus, and `allocatedMaskedCoefficientDensity … mask` is that density on the cover multiplied by the mask.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedMaskedCoefficientDensity_sample_ae_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedMaskedCoefficientDensity_sample_ae` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedMaskedCoefficientSampleAE.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B097`, `OAIE3v2B100` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedMaskedCoefficientSampleAE.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedMaskedCoefficientDensity_sample_ae)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B097
import Definitions.Def_OAIE3v2B100

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)]
variable [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedMaskedCoefficientDensity_sample_ae_s2
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → ℝ) :
    ∀ᵐ z ∂(allocatedCoefficientSource B U b hR hσ S).prod
      (PMF.uniformOfFintype (CoefficientDeckResidues
        (K := LayerSamplerVariables G I n B) E q)).toMeasure,
      allocatedMaskedCoefficientDensity B U b o S q
          (coefficientDeckResidueMask U bW b hb q test)
          (canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) z.1 z.2) =
        test (coefficientSamplerChartResidues q z.1 z.2) *
          allocatedCoefficientDensity B U b hb o hR hσ S
            (quotientIntegerCover (coefficientIntegerLattice U) q
              (canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) z.1 z.2)) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
