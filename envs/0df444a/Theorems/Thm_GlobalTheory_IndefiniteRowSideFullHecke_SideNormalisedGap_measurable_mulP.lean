-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SideNormalisedGap_measurable_mulP
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap.measurable_mulP
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:32:21.48237+00:00
-- url     : https://prove2.me/theorems/49e590b8-921f-4e01-b098-162e34061e84
-- title:
--   Side Normalised Gap: measurable mul P
-- statement:
--   The Side Normalised Gap construction uses the measurable mul P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SideNormalisedGap.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SideNormalisedGap.lean#L49-L54

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SideNormalisedGap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap
open MeasureTheory Matrix
open scoped InnerProductSpace
open PI.UpqRep (IsDSHpk IsLowUnitH IsHCTypeW IsKFinHpk IsCayleyU IsOrthProjOnto InLieHpk lowKSub smoothVecs dsigW)
open Formalism.QuantumDeterminants (Mt UH Hpk Nset UWset inWb Tz IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)

theorem GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap.measurable_mulP {k r : ℕ} : Measurable (mulP (k := k) (r := r)) := by sorry
