-- Prove2me | Theorems.Thm_HostParam_Seam_exists_host
-- name    : HostParam.Seam.exists_host
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:02.398398+00:00
-- url     : https://prove2.me/theorems/e006d8c9-f170-49bc-ba8b-ecfc3b5e73b8
-- title:
--   Seam: exists host
-- statement:
--   The Seam construction uses the exists host property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CoprimeRanks/SecondSetNoRelation.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CoprimeRanks/SecondSetNoRelation.lean#L100-L104

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Development_AutomorphicArithmetic_CoprimeRanks_SecondSetNoRelation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HC Formalism.BasicNotions
open scoped Pointwise
noncomputable section
open HostParam HostParam.Seam

theorem HostParam.Seam.exists_host (R : Ranks) (H : HostAx R.toFrame) {b : ℕ} (h : FieldRows H.toHostRaw b)
    (hq : 4 * R.t * R.r + 1 < H.q ∧ 4 * R.t * R.r + 1 < H.d) (c : Choices R.toFrame H.toHostRaw) :
    ∃ D : Formalism.BasicNotions.Host R, D.toHostAx = H ∧ D.splitBound = b ∧ HEq (HostNF.ofHost D).ch c := by sorry
