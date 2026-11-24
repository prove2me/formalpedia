-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSChainAdj_term_adj
-- name    : GlobalTheory.CompanionTheory.DSChainAdj.term_adj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:34.257424+00:00
-- url     : https://prove2.me/theorems/67df3cea-770c-42dd-9ad3-43a68d06be0e
-- title:
--   DSChain Adj: term adj
-- statement:
--   The DSChain Adj construction uses the term adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SumInsertErase.lean#L48-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SumInsertErase.lean#L48-L65

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

theorem GlobalTheory.CompanionTheory.DSChainAdj.term_adj (i : NC ε) (T T' : Module.End ℂ V) (h : ∀ x y : V, ⟪T x, y⟫_ℂ = -⟪x, T' y⟫_ℂ) (w x : Ch ε V) :
    ip (lift ε T (ann i w)) x = -ip w (lift ε T' (cre i x)) := by sorry
