-- Prove2me | Theorems.Thm_GlobalTheory_tsum_transversal_eq_tsum_orbitQuotient
-- name    : GlobalTheory.tsum_transversal_eq_tsum_orbitQuotient
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:46:50.661388+00:00
-- url     : https://prove2.me/theorems/e5233142-934d-46ec-99df-ea8c6e315c99
-- title:
--   Global Theory: tsum transversal eq tsum orbit Quotient
-- statement:
--   The Global Theory construction uses the tsum transversal eq tsum orbit Quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TsumTransversalEqTsumOrbitQuotientGeneral.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TsumTransversalEqTsumOrbitQuotientGeneral.lean#L44-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TsumTransversalEqTsumOrbitQuotientGeneral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal Classical
open GlobalTheory

theorem GlobalTheory.tsum_transversal_eq_tsum_orbitQuotient : ∀ {G X A : Type} [Group G] [MulAction G X] (ι : A → X) (T : X → Prop), (∀ g : G, ∀ x, T x → T (g • x)) → (∀ a, T (ι a)) → (∀ x, T x → ∃ a, ∃ g : G, g • ι a = x) → (∀ a b, (∃ g : G, g • ι a = ι b) → a = b) → (∀ φ : X → ℂ, (∀ g : G, ∀ x, T x → φ (g • x) = φ x) → ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0) ∧ ∀ φ : X → ℝ≥0∞, (∀ g : G, ∀ x, T x → φ (g • x) = φ x) → ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0 := by sorry
