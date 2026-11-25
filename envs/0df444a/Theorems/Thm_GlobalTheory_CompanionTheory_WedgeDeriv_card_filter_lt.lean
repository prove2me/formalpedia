-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeDeriv_card_filter_lt
-- name    : GlobalTheory.CompanionTheory.WedgeDeriv.card_filter_lt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:27:53.663465+00:00
-- url     : https://prove2.me/theorems/1d741999-d0e2-4c7e-a5fb-795fb14fe360
-- title:
--   Wedge Deriv: card filter lt
-- statement:
--   The Wedge Deriv construction uses the card filter lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorDifferentialMatrixUnitFormula.lean#L56-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorDifferentialMatrixUnitFormula.lean#L56-L66

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

theorem GlobalTheory.CompanionTheory.WedgeDeriv.card_filter_lt {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) (i : Fin m) :
    (((univ.image f).erase (f i)).filter fun c => c < f i).card = i := by sorry
