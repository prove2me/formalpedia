-- Prove2me | Theorems.Thm_GlobalTheory_TorsionZero_exists_homogenisation
-- name    : GlobalTheory.TorsionZero.exists_homogenisation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:55.568268+00:00
-- url     : https://prove2.me/theorems/76d825be-c3d6-4291-a3fb-3b896410dc27
-- title:
--   Torsion Zero: exists homogenisation
-- statement:
--   The Torsion Zero construction uses the exists homogenisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/NonemptyGradedAlgebraSubGrading.lean#L26-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionZero
open MvPolynomial
variable {K σ : Type} [Field K]

theorem GlobalTheory.TorsionZero.exists_homogenisation (F : MvPolynomial σ K) (i : σ) :
    ∃ (n : ℕ) (G : MvPolynomial σ K), G.IsHomogeneous n ∧
      ∀ (S : Type) [CommRing S] [Algebra K S] (a : σ → S), a i = 1 → aeval a G = aeval a F := by sorry
