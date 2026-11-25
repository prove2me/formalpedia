-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryZariskiDense_unitary_zariski_dense
-- name    : GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:55:51.992108+00:00
-- url     : https://prove2.me/theorems/78c0d706-4fc6-4472-983f-da8d4706bc33
-- title:
--   Unitary Zariski Dense: unitary zariski dense
-- statement:
--   The Unitary Zariski Dense construction uses the unitary zariski dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L210-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L210-L259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
variable {ι : Type} {a : ℕ}
variable [Fintype ι]

theorem GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense : ∀ {ι : Type} [Fintype ι] {a : ℕ} (Q : MvPolynomial (ι × Fin a × Fin a) ℂ),
    (∀ g : ι → Matrix.unitaryGroup (Fin a) ℂ,
      MvPolynomial.eval (fun v : ι × Fin a × Fin a => (g v.1 : Matrix (Fin a) (Fin a) ℂ) v.2.1 v.2.2) Q = 0) →
    Q = 0 := by sorry
