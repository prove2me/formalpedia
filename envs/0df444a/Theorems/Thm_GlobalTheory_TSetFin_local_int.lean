-- Prove2me | Theorems.Thm_GlobalTheory_TSetFin_local_int
-- name    : GlobalTheory.TSetFin.local_int
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:01:18.96789+00:00
-- url     : https://prove2.me/theorems/eae8bc30-7d9f-449f-bf67-00ad7af2d5b8
-- title:
--   TSet Fin: local int
-- statement:
--   The TSet Fin construction uses the local int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel.lean#L25-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel.lean#L25-L39

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

theorem GlobalTheory.TSetFin.local_int {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (ϖ : v.adicCompletion F) (k : ℕ) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (a a' b b' g g' : GL (Fin n) (v.adicCompletion F))
    (ha' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hai : ∀ i j, Valued.v (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hbi : ∀ i j, Valued.v (((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hb' : ∀ i j, Valued.v ((b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hc : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j -
      (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1)
    (hg : (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)))
    (hg' : (g' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F))) :
    ∀ i j, Valued.v (((g⁻¹ * g' : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 := by sorry
