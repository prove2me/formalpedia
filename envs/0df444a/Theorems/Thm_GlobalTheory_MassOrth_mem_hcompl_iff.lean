-- Prove2me | Theorems.Thm_GlobalTheory_MassOrth_mem_hcompl_iff
-- name    : GlobalTheory.MassOrth.mem_hcompl_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:29.588725+00:00
-- url     : https://prove2.me/theorems/e4281bd9-121b-4512-b597-dc0fe5f4c88b
-- title:
--   Mass Orth: mem hcompl iff
-- statement:
--   The Mass Orth construction uses the mem hcompl iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L190-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L190-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
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
open GlobalTheory GlobalTheory.MassOrth
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] [StarRing K]
omit [NumberField K]

theorem GlobalTheory.MassOrth.mem_hcompl_iff (P : Ideal (𝓞 K)) (hP : P.IsPrime) (s : 𝓞 K) :
    s ∈ hcompl (K := K) P ↔ s ∉ P ∧ starInt s ∉ P := by sorry
