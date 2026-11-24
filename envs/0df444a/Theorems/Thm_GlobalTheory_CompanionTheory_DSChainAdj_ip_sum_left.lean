-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSChainAdj_ip_sum_left
-- name    : GlobalTheory.CompanionTheory.DSChainAdj.ip_sum_left
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:36.234269+00:00
-- url     : https://prove2.me/theorems/bce0fdb8-0c64-485a-919c-290614c9a646
-- title:
--   DSChain Adj: ip sum left
-- statement:
--   The DSChain Adj construction uses the ip sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SumInsertErase.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SumInsertErase.lean#L67-L72

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem GlobalTheory.CompanionTheory.DSChainAdj.ip_sum_left {ι : Type} (s : Finset ι) (f : ι → Ch ε V) (x : Ch ε V) :
    ip (∑ i ∈ s, f i) x = ∑ i ∈ s, ip (f i) x := by sorry
