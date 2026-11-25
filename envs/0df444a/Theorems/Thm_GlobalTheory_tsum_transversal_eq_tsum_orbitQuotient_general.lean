-- Prove2me | Theorems.Thm_GlobalTheory_tsum_transversal_eq_tsum_orbitQuotient_general
-- name    : GlobalTheory.tsum_transversal_eq_tsum_orbitQuotient_general
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:25:37.321181+00:00
-- url     : https://prove2.me/theorems/9d30371f-a705-54ad-9a8b-f62841d06d60
-- title:
--   Global Theory: tsum transversal eq tsum orbit Quotient general
-- statement:
--   The Global Theory construction uses the tsum transversal eq tsum orbit Quotient general property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TsumTransversalEqTsumOrbitQuotientGeneral.lean#L6-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TsumTransversalEqTsumOrbitQuotientGeneral.lean#L6-L42

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

theorem GlobalTheory.tsum_transversal_eq_tsum_orbitQuotient_general {G X A M : Type} [Group G] [MulAction G X]
    [AddCommMonoid M] [TopologicalSpace M] (ι : A → X) (T : X → Prop)
    (hT : ∀ g : G, ∀ x, T x → T (g • x)) (hι : ∀ a, T (ι a))
    (hsurj : ∀ x, T x → ∃ a, ∃ g : G, g • ι a = x)
    (hinj : ∀ a b, (∃ g : G, g • ι a = ι b) → a = b)
    (φ : X → M) (hφ : ∀ g : G, ∀ x, T x → φ (g • x) = φ x) :
    ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0 := by sorry
