-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_exists_independent_torsion_prime
-- name    : GroundTheory.Arith.Abelian.exists_independent_torsion_prime
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:27:11.849874+00:00
-- url     : https://prove2.me/theorems/ec3addf8-43ce-4af0-b037-44cc6f69e19d
-- title:
--   Abelian: exists independent torsion prime
-- statement:
--   The Abelian construction uses the exists independent torsion prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L303-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateModule.lean#L303-L320

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open AddSubgroup
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem GroundTheory.Arith.Abelian.exists_independent_torsion_prime (hℓF : (ℓ : F) ≠ 0) :
    ∃ P Q : W.toAffine.Point, ℓ • P = 0 ∧ ℓ • Q = 0 ∧
      ∀ a b : ℕ, a • P + b • Q = 0 → ℓ ∣ a ∧ ℓ ∣ b := by sorry
