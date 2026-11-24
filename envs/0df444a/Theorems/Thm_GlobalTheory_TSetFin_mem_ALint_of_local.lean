-- Prove2me | Theorems.Thm_GlobalTheory_TSetFin_mem_ALint_of_local
-- name    : GlobalTheory.TSetFin.mem_ALint_of_local
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:01:51.9338+00:00
-- url     : https://prove2.me/theorems/16db43ed-dcf5-44fc-8505-dfa304870cab
-- title:
--   TSet Fin: mem ALint of local
-- statement:
--   The TSet Fin construction uses the mem ALint of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel.lean#L20-L23

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HeckeDoubleCosetAdicCompletionInvMulIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut
noncomputable section
open GlobalTheory GlobalTheory.TSetFin
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => maximalRealSubfield L

theorem GlobalTheory.TSetFin.mem_ALint_of_local (s : SplitPlace L) (e : 𝓞 L) (he : Valued.v (s.i (e : L)) = 1)
    (he' : Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1) (z : AL L)
    (hz : ∀ w, w ≠ s.v → compAt L w z = 0) (h1 : Valued.v (s.proj z) ≤ 1)
    (h2 : Valued.v (s.proj (conjAL L z)) ≤ 1) : z ∈ ALint L := by sorry
