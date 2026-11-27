-- Prove2me | Theorems.Thm_HostParam_Seam_HostNF_ofHost_toHost
-- name    : HostParam.Seam.HostNF.ofHost_toHost
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:03:00.465725+00:00
-- url     : https://prove2.me/theorems/6ca20c05-312a-5c50-a38c-e79ba2064a52
-- title:
--   Host NF: of Host to Host
-- statement:
--   The Host NF construction uses the of Host to Host property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CoprimeRanks/SecondSetNoRelation.lean#L85-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CoprimeRanks/SecondSetNoRelation.lean#L85-L85

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

theorem HostParam.Seam.HostNF.ofHost_toHost {R : Ranks} (N : HostNF R) : HostNF.ofHost N.toHost = N := by sorry
