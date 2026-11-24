-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_det_sq_conjugateHom
-- name    : GlobalTheory.EigenSplit.det_sq_conjugateHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:39.542491+00:00
-- url     : https://prove2.me/theorems/e587dc34-3be0-441a-9e74-a9a1319d8df6
-- title:
--   Eigen Split: det sq conjugate Hom
-- statement:
--   The Eigen Split construction uses the det sq conjugate Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L748-L755
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L748-L755

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

theorem GlobalTheory.EigenSplit.det_sq_conjugateHom {L : Type*} [Field L] [Algebra (𝓞 L) R] {φ : ι → E →+* L}
    (hφ : Function.Injective φ) (b : Module.Basis ι ℤ (𝓞 E)) :
    (Matrix.of fun i j => conjugateHom L R (φ i) (b j)).det ^ 2 = (NumberField.discr E : R) := by sorry
