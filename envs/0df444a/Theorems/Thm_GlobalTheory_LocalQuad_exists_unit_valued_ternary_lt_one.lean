-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_exists_unit_valued_ternary_lt_one
-- name    : GlobalTheory.LocalQuad.exists_unit_valued_ternary_lt_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:07:27.807563+00:00
-- url     : https://prove2.me/theorems/4961032d-4312-4d54-9f8e-77e5fa37aa99
-- title:
--   Local Quad: exists unit valued ternary lt one
-- statement:
--   The Local Quad construction uses the exists unit valued ternary lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitValuedTernaryLtOne.lean#L26-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitValuedTernaryLtOne.lean#L26-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNonzeroIsotropic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuedTernaryLtOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad

theorem GlobalTheory.LocalQuad.exists_unit_valued_ternary_lt_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (c : Fin 3 → Fin 3 → v.adicCompletion F)
    (hc : ∀ i j, Valued.v (c i j) ≤ 1) :
    ∃ x : Fin 3 → v.adicCompletion F, (∀ i, Valued.v (x i) ≤ 1) ∧ (∃ i, Valued.v (x i) = 1) ∧
      Valued.v (∑ i, ∑ j, c i j * x i * x j) < 1 := by sorry
