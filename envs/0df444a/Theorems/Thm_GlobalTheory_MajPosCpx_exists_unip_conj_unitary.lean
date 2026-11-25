-- Prove2me | Theorems.Thm_GlobalTheory_MajPosCpx_exists_unip_conj_unitary
-- name    : GlobalTheory.MajPosCpx.exists_unip_conj_unitary
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:11.40237+00:00
-- url     : https://prove2.me/theorems/46621a23-2377-4b78-ac01-795e9187c7d1
-- title:
--   Maj Pos Cpx: exists unip conj unitary
-- statement:
--   The Maj Pos Cpx construction uses the exists unip conj unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComplexWittBasisNormalForm.lean#L22-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComplexWittBasisNormalForm.lean#L22-L171

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjTransposeMulMulSelfOfUnitaryConjStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefExistsConjTransposeMulMulEqOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RadicalEltMovingDualToMajorantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLeviElementIsotropicOrthogonalComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFlagComplementPosDefFactorizationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFlagUnipotentMatrixExistsSparseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexWittBasisNormalForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
open GlobalTheory GlobalTheory.MajPosCpx

theorem GlobalTheory.MajPosCpx.exists_unip_conj_unitary : ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J →
    ∀ (X Y : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * X = 0 → Y.conjTranspose * J * Y = 0 → X.conjTranspose * J * Y = 1 →
    ∀ (c : GL (Fin n) ℂ) (ε : Fin n → Bool), (c.1).conjTranspose * J * c.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) →
    ∀ (l d : ℕ) (h : l + d ≤ r),
      ∃ (u : GL (Fin n) ℂ) (N : Matrix (Fin r) (Fin r) ℂ),
        (u.1).conjTranspose * J * u.1 = J ∧ u.1 * X = X + X * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → ℂ, (∀ i : Fin r, i.val < l + d → Matrix.mulVec (X.conjTranspose * J) v i = 0) →
          ∃ w : Fin r → ℂ, (∀ i, w i ≠ 0 → i.val < l + d) ∧ Matrix.mulVec u.1 v - v = Matrix.mulVec X w) ∧
        ∃ y₀ : GL (Fin d) ℂ, ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
          let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
          let Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩
          let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
          let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
          let M : Matrix (Fin n) (Fin n) ℂ := (c⁻¹).1 * u.1 * G * (u⁻¹).1 * c.1
          M.conjTranspose * M = 1 := by sorry
