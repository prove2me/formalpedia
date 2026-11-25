-- Prove2me | Theorems.Thm_GlobalTheory_Jets_addOf_eps
-- name    : GlobalTheory.Jets.addOf_eps
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:52:36.343628+00:00
-- url     : https://prove2.me/theorems/a73650bd-df08-41ea-987b-4e7310237e92
-- title:
--   Jets: add Of eps
-- statement:
--   The Jets construction uses the add Of eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HasSubstAddSqZero.lean#L125-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HasSubstAddSqZero.lean#L125-L157

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ContinuousPderivDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.Jets

theorem GlobalTheory.Jets.addOf_eps {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (v : Fin d → R) (j : Fin d) :
    addOf (n := 1) (G.mapF (algebraMap R (DualNumber R))) (pt (DualNumber R) d 0)
        (fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R)) j =
      X ((0 : Fin 1), j) + C (DualNumber.eps : DualNumber R) *
        MvPowerSeries.map (algebraMap R (DualNumber R))
          (∑ i : Fin d, C (v i) *
            ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F j))) := by sorry
