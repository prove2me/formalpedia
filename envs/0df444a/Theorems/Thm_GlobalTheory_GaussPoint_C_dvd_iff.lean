-- Prove2me | Theorems.Thm_GlobalTheory_GaussPoint_C_dvd_iff
-- name    : GlobalTheory.GaussPoint.C_dvd_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:58:30.576803+00:00
-- url     : https://prove2.me/theorems/dd71dcf4-f1ea-4aa2-af04-20d46251a5f1
-- title:
--   Gauss Point: C dvd iff
-- statement:
--   The Gauss Point construction uses the C dvd iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGaussPoint.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGaussPoint.lean#L9-L19

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGaussPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj IsLocalRing
open GlobalTheory GlobalTheory.GaussPoint

theorem GlobalTheory.GaussPoint.C_dvd_iff {V : Type*} [CommRing V] (a : V) (f : PowerSeries V) :
    PowerSeries.C a ∣ f ↔ ∀ n, a ∣ PowerSeries.coeff n f := by sorry
