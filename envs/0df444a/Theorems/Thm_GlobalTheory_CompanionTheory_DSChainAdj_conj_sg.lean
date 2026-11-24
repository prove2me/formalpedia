-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSChainAdj_conj_sg
-- name    : GlobalTheory.CompanionTheory.DSChainAdj.conj_sg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:24.113892+00:00
-- url     : https://prove2.me/theorems/7ae0315f-85e0-44fd-af81-9757e65c765f
-- title:
--   DSChain Adj: conj sg
-- statement:
--   The DSChain Adj construction uses the conj sg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SumInsertErase.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SumInsertErase.lean#L18-L20

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SumInsertErase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSChainAdj
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool}

theorem GlobalTheory.CompanionTheory.DSChainAdj.conj_sg (i : NC ε) (A : Finset (NC ε)) : (starRingEnd ℂ) (sg i A) = sg i A := by sorry
