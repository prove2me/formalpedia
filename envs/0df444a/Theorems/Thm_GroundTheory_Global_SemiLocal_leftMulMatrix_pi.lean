-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_leftMulMatrix_pi
-- name    : GroundTheory.Global.SemiLocal.leftMulMatrix_pi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:26:32.258257+00:00
-- url     : https://prove2.me/theorems/7ec6c861-ef20-4680-a05d-8c3cdd7ccf0a
-- title:
--   Semi Local: left Mul Matrix pi
-- statement:
--   The Semi Local construction uses the left Mul Matrix pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/NormTrace.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/NormTrace.lean#L31-L40

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Matrix
noncomputable section
open GroundTheory.Global.SemiLocal
variable {R : Type*} [Field R] {ι : Type*} [Fintype ι] {S : ι → Type*} [∀ i, CommRing (S i)]
  [∀ i, Algebra R (S i)] [∀ i, Module.Finite R (S i)]
omit [∀ i, Module.Finite R (S i)]

theorem GroundTheory.Global.SemiLocal.leftMulMatrix_pi [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    [∀ i, DecidableEq (κ i)] (b : ∀ i, Basis (κ i) R (S i)) (x : ∀ i, S i) :
    Algebra.leftMulMatrix (Pi.basis b) x =
      blockDiagonal' fun i ↦ Algebra.leftMulMatrix (b i) (x i) := by sorry
