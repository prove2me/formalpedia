-- Prove2me | Theorems.Thm_GlobalTheory_Per_X_dvd_ev_iff
-- name    : GlobalTheory.Per.X_dvd_ev_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:03:26.579655+00:00
-- url     : https://prove2.me/theorems/3e091cdb-771f-46ac-96d4-159df46a2491
-- title:
--   Per: X dvd ev iff
-- statement:
--   The Per construction uses the X dvd ev iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ProdPrimePowDvd.lean#L38-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ProdPrimePowDvd.lean#L38-L58

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

theorem GlobalTheory.Per.X_dvd_ev_iff (hinj : Function.Injective (algebraMap O L)) {x : O} (hx : ¬ IsUnit x)
    (ev : PowerSeries O →ₐ[O] PowerSeries L) {w : PowerSeries L}
    (hev : ev PowerSeries.X = PowerSeries.C (algebraMap O L x) + PowerSeries.X * w)
    (a : PowerSeries O) :
    PowerSeries.X ∣ ev a ↔ (PowerSeries.X - PowerSeries.C x) ∣ a := by sorry
