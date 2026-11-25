-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeDeriv_dR_wedge
-- name    : GlobalTheory.CompanionTheory.WedgeDeriv.dR_wedge
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:24:35.446597+00:00
-- url     : https://prove2.me/theorems/5dc4293b-7e5b-5fe0-bfda-f1441eff6aa6
-- title:
--   Wedge Deriv: d R wedge
-- statement:
--   The Wedge Deriv construction uses the d R wedge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorDifferentialMatrixUnitFormula.lean#L125-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorDifferentialMatrixUnitFormula.lean#L125-L132

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialMatrixUnitFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeDeriv

theorem GlobalTheory.CompanionTheory.WedgeDeriv.dR_wedge (k r m : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (J J' : Sub (2 * r + k + 1) m) :
    (wedge k r m).dR X J J' = ∑ j, ∑ i, adjugate ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).submatrix (J.1.orderEmbOfFin J.2)
      (J'.1.orderEmbOfFin J'.2)) j i * X (J.1.orderEmbOfFin J.2 i) (J'.1.orderEmbOfFin J'.2 j) := by sorry
