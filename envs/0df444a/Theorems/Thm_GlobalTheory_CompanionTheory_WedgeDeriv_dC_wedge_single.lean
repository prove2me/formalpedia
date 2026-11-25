-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeDeriv_dC_wedge_single
-- name    : GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:28:05.797444+00:00
-- url     : https://prove2.me/theorems/1f567ead-2ea1-41ec-b189-0284322a3fae
-- title:
--   Wedge Deriv: d C wedge single
-- statement:
--   The Wedge Deriv construction uses the d C wedge single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorDifferentialMatrixUnitFormula.lean#L141-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorDifferentialMatrixUnitFormula.lean#L141-L152

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

theorem GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single : ∀ (k r m : ℕ) (a b : Fin (2 * r + k + 1)) (J J' : Sub (2 * r + k + 1) m), (wedge k r m).dC (Matrix.single a b 1) J J' = if b ∈ J'.1 ∧ a ∉ J'.1.erase b ∧ J.1 = insert a (J'.1.erase b) then (-1) ^ ((J'.1.erase b).filter fun c => c < a).card * (-1) ^ ((J'.1.erase b).filter fun c => c < b).card else 0 := by sorry
