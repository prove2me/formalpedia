-- Prove2me | Theorems.Thm_GlobalTheory_exists_numerator_of_involution
-- name    : GlobalTheory.exists_numerator_of_involution
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:34.642807+00:00
-- url     : https://prove2.me/theorems/a919e5f6-05a2-4be2-90b1-e4c797dab4fe
-- title:
--   Global Theory: exists numerator of involution
-- statement:
--   The Global Theory construction uses the exists numerator of involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNumeratorOfInvolution.lean#L11-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNumeratorOfInvolution.lean#L11-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Polynomial
open scoped Topology
noncomputable section
open GlobalTheory

theorem GlobalTheory.exists_numerator_of_involution {F ι : Type*} [Field F] [CharZero F] [Fintype ι]
    (σ : ι → ι) (hσ : ∀ t, σ (σ t) = t) (p a b : ι → F)
    (hp : ∀ s t, p s = p t ↔ s = t ∨ s = σ t) (hb : ∀ t, b (σ t) = b t)
    (hb0 : ∀ t, b t = 0 ↔ σ t = t) (ha : ∀ t, σ t = t → a t ≠ 0)
    (R : Subring F[X]) (hX : X ∈ R) (hR : ∀ t, C (p t) ∈ R ∧ C (a t) ∈ R ∧ C (b t) ∈ R) :
    ∃ A ∈ R, A.Monic ∧ A.natDegree = Fintype.card ι + 1 ∧ IsCoprime A (∏ t, (X - C (p t))) ∧
      ∀ x, (∀ t, x ≠ p t) → A.eval x =
        (∏ t, (x - p t)) * (x + ∑ t, (a t / (x - p t) + b t / (x - p t) ^ 2)) := by sorry
