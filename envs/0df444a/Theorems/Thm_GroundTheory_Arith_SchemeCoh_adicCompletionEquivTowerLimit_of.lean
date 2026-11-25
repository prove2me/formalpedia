-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_adicCompletionEquivTowerLimit_of
-- name    : GroundTheory.Arith.SchemeCoh.adicCompletionEquivTowerLimit_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:12.046913+00:00
-- url     : https://prove2.me/theorems/122ea595-2ee7-5103-95f0-fe6bd151a89f
-- title:
--   Scheme Coh: adic Completion Equiv Tower Limit of
-- statement:
--   The Scheme Coh construction uses the adic Completion Equiv Tower Limit of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L264-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean#L264-L267

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_FormalLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {A : Type u} [CommRing A] (I : Ideal A) {H : Type u} [AddCommGroup H] [Module A H]
  (K : ℕ → Submodule A H) (hK : Antitone K)
variable {I K}

theorem GroundTheory.Arith.SchemeCoh.adicCompletionEquivTowerLimit_of (h₁ : ∀ n, I ^ (n + 1) • (⊤ : Submodule A H) ≤ K n)
    {c : ℕ} (h₂ : ∀ n, K (n + c) ≤ I ^ n • (⊤ : Submodule A H)) (h : H) (n : ℕ) :
    (adicCompletionEquivTowerLimit hK h₁ h₂ (AdicCompletion.of I H h)).1 n =
      Submodule.Quotient.mk h := by sorry
