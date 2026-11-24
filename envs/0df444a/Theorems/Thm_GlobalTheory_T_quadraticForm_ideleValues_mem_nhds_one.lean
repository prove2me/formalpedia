-- Prove2me | Theorems.Thm_GlobalTheory_T_quadraticForm_ideleValues_mem_nhds_one
-- name    : GlobalTheory.T.quadraticForm_ideleValues_mem_nhds_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:20:43.02988+00:00
-- url     : https://prove2.me/theorems/1124c9cb-85f1-4f0c-91f2-b9dc9558f3f2
-- title:
--   T: quadratic Form idele Values mem nhds one
-- statement:
--   The T construction uses the quadratic Form idele Values mem nhds one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/QuadraticFormIdeleValuesMemNhdsOneStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/QuadraticFormIdeleValuesMemNhdsOneStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticFormIdeleValuesMemNhdsOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticFormIdeleValuesMemNhdsOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.quadraticForm_ideleValues_mem_nhds_one : ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → {a : (AdeleRing (𝓞 F) F)ˣ | ∃ x y : AdeleRing (𝓞 F) F, (a : AdeleRing (𝓞 F) F) = x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2} ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F)ˣ) := by sorry
