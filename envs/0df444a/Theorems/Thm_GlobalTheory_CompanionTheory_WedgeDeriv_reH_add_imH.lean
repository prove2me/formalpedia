-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeDeriv_reH_add_imH
-- name    : GlobalTheory.CompanionTheory.WedgeDeriv.reH_add_imH
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:40.68394+00:00
-- url     : https://prove2.me/theorems/c45621ae-9a03-4d2b-87ff-0df3927a6aad
-- title:
--   Wedge Deriv: re H add im H
-- statement:
--   The Wedge Deriv construction uses the re H add im H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorDifferentialMatrixUnitFormula.lean#L134-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorDifferentialMatrixUnitFormula.lean#L134-L139

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

theorem GlobalTheory.CompanionTheory.WedgeDeriv.reH_add_imH (k r : ℕ) (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : reH k r Y + Complex.I • imH k r Y = Y := by sorry
