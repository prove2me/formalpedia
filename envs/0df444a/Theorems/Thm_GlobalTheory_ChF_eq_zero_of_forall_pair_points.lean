-- Prove2me | Theorems.Thm_GlobalTheory_ChF_eq_zero_of_forall_pair_points
-- name    : GlobalTheory.ChF.eq_zero_of_forall_pair_points
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:02.262828+00:00
-- url     : https://prove2.me/theorems/27cd5567-c940-4f7e-9684-f802a9716854
-- title:
--   Ch F: eq zero of forall pair points
-- statement:
--   The Ch F construction uses the eq zero of forall pair points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EqZeroOfForallPairPointsValuationIntegers.lean#L99-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EqZeroOfForallPairPointsValuationIntegers.lean#L99-L123

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesEvalOfPowMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemSupSpanXPowIffAndIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOfForallPairPointsValuationIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ChF
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {O : Type} [CommRing O] {d : ℕ}

theorem GlobalTheory.ChF.eq_zero_of_forall_pair_points (W : (PS O 1 d →ₐ[O] O) → Prop)
    (hW : ∀ f : PS O 1 d, (∀ φ, W φ → φ f = 0) → f = 0) (f : PS O 2 d)
    (hf : ∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O),
      (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) →
        W φ → W φ' → Φ f = 0) : f = 0 := by sorry
