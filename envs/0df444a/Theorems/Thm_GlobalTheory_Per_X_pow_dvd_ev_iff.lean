-- Prove2me | Theorems.Thm_GlobalTheory_Per_X_pow_dvd_ev_iff
-- name    : GlobalTheory.Per.X_pow_dvd_ev_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:49:53.806926+00:00
-- url     : https://prove2.me/theorems/c2bdd3bf-58fd-4b1b-b96e-f59745feac45
-- title:
--   Per: X pow dvd ev iff
-- statement:
--   The Per construction uses the X pow dvd ev iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ProdPrimePowDvd.lean#L60-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ProdPrimePowDvd.lean#L60-L82

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProdPrimePowDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.Per
variable {O : Type} [CommRing O] [IsLocalRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {L : Type} [Field L] [Algebra O L]

theorem GlobalTheory.Per.X_pow_dvd_ev_iff (hinj : Function.Injective (algebraMap O L)) {x : O} (hx : ¬ IsUnit x)
    (ev : PowerSeries O →ₐ[O] PowerSeries L) {w : PowerSeries L} (hw : IsUnit w)
    (hev : ev PowerSeries.X = PowerSeries.C (algebraMap O L x) + PowerSeries.X * w)
    (m : ℕ) (a : PowerSeries O) :
    PowerSeries.X ^ m ∣ ev a ↔ (PowerSeries.X - PowerSeries.C x) ^ m ∣ a := by sorry
