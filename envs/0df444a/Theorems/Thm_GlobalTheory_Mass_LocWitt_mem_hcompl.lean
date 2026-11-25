-- Prove2me | Theorems.Thm_GlobalTheory_Mass_LocWitt_mem_hcompl
-- name    : GlobalTheory.Mass.LocWitt.mem_hcompl
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:59:53.22696+00:00
-- url     : https://prove2.me/theorems/42cc800f-5a88-43c3-8eb8-0bdeacf3c46f
-- title:
--   Loc Witt: mem hcompl
-- statement:
--   The Loc Witt construction uses the mem hcompl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemHcompl.lean#L170-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemHcompl.lean#L170-L180

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LocWitt

theorem GlobalTheory.Mass.LocWitt.mem_hcompl {K : Type} [Field K] [NumberField K] [StarRing K] {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : conjIdeal (K := K) P = P) (s : 𝓞 K) :
    s ∈ hcompl (K := K) P ↔ s ∉ P := by sorry
