-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_exists_isotropic_diagonal
-- name    : GlobalTheory.UTrans.exists_isotropic_diagonal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:22:56.029348+00:00
-- url     : https://prove2.me/theorems/90becc3e-f239-44d8-a545-379fdad97c15
-- title:
--   UTrans: exists isotropic diagonal
-- statement:
--   The UTrans construction uses the exists isotropic diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsotropicOfIndefinite.lean#L29-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsotropicOfIndefinite.lean#L29-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__LandherrStIffLandherr_9fec213082f17e18
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicOfIndefinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.UTrans
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.UTrans.exists_isotropic_diagonal {n : ℕ} (hn : 3 ≤ n) {g : Fin n → E}
    (hg : ∀ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (g i) = g i) (hg0 : ∀ i, g i ≠ 0)
    (hs : ∀ τ : E →+* ℂ, (∃ i, 0 < (τ (g i)).re) ∧ ∃ j, (τ (g j)).re < 0) :
    ∃ z : Fin n → E, z ≠ 0 ∧ _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal g) z z = 0 := by sorry
