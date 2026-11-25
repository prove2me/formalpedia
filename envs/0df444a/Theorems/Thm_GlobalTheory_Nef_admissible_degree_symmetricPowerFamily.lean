-- Prove2me | Theorems.Thm_GlobalTheory_Nef_admissible_degree_symmetricPowerFamily
-- name    : GlobalTheory.Nef.admissible_degree_symmetricPowerFamily
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:40.247699+00:00
-- url     : https://prove2.me/theorems/8ddaf16a-2281-4ede-a7bb-9ea4cb85e544
-- title:
--   Nef: admissible degree symmetric Power Family
-- statement:
--   The Nef construction uses the admissible degree symmetric Power Family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdmissibleDegreeSymmetricPowerFamily.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdmissibleDegreeSymmetricPowerFamily.lean#L59-L67

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistAtOfNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdmissibleDegreeSymmetricPowerFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial
set_option autoImplicit false
open GlobalTheory GlobalTheory.Nef

theorem GlobalTheory.Nef.admissible_degree_symmetricPowerFamily : ∀ (k F : Type) [Field k] [IsAlgClosed k] [Field F] [Algebra k F] (m : ℕ)
    (g : Place k F → Matrix (Fin 2) (Fin 2) F), admitted g → (∀ v, g v 1 0 = 0) →
      admitted (fun v => symMat m (g v)) ∧ deg (fun v => symMat m (g v)) = ((m * (m + 1) / 2 : ℕ) : ℤ) * deg g := by sorry
