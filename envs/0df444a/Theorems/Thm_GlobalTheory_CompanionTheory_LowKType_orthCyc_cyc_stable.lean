-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LowKType_orthCyc_cyc_stable
-- name    : GlobalTheory.CompanionTheory.LowKType.orthCyc_cyc_stable
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:52:04.639777+00:00
-- url     : https://prove2.me/theorems/520bce7d-b559-4653-8d35-2f8f178715f3
-- title:
--   Low KType: orth Cyc cyc stable
-- statement:
--   The Low KType construction uses the orth Cyc cyc stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OrthCycCycStable.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OrthCycCycStable.lean#L11-L16

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OrthCycCycStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LowKType
open CompanionTheory.D.LK CompanionTheory.D.DSIC Formalism.REAL

theorem GlobalTheory.CompanionTheory.LowKType.orthCyc_cyc_stable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (a b : Fin n) {x : V} (hx : x ∈ Cyc E v) :
    E a b x ∈ Cyc E v := by sorry
