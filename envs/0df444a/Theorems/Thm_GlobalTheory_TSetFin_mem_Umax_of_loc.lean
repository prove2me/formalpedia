-- Prove2me | Theorems.Thm_GlobalTheory_TSetFin_mem_Umax_of_loc
-- name    : GlobalTheory.TSetFin.mem_Umax_of_loc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:01:58.779449+00:00
-- url     : https://prove2.me/theorems/ada22e57-085b-47ae-9154-93bcfcf17d01
-- title:
--   TSet Fin: mem Umax of loc
-- statement:
--   The TSet Fin construction uses the mem Umax of loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel.lean#L57-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel.lean#L57-L89

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

theorem GlobalTheory.TSetFin.mem_Umax_of_loc {n : ℕ} (s : SplitPlace L) (x : GA L n) (hx : TrivOutside {s.v} x)
    (h1 : ∀ i j, Valued.v (((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1) :
    x ∈ Umax L n := by sorry
