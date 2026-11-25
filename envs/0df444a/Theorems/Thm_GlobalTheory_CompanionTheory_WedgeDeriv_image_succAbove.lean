-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeDeriv_image_succAbove
-- name    : GlobalTheory.CompanionTheory.WedgeDeriv.image_succAbove
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:24:35.800107+00:00
-- url     : https://prove2.me/theorems/56733acd-b879-5028-8a81-c72c395754a7
-- title:
--   Wedge Deriv: image succ Above
-- statement:
--   The Wedge Deriv construction uses the image succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorDifferentialMatrixUnitFormula.lean#L68-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorDifferentialMatrixUnitFormula.lean#L68-L77

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

theorem GlobalTheory.CompanionTheory.WedgeDeriv.image_succAbove {m n : ℕ} (f : Fin (m + 1) → Fin n) (hf : StrictMono f) (i : Fin (m + 1)) :
    univ.image (f ∘ i.succAbove) = (univ.image f).erase (f i) := by sorry
