-- Prove2me | Theorems.Thm_GlobalTheory_ShortVectors_transference_rat
-- name    : GlobalTheory.ShortVectors.transference_rat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:11:37.463283+00:00
-- url     : https://prove2.me/theorems/df9c673b-bd2b-4ca6-b04f-6b1cfbfdfdc8
-- title:
--   Short Vectors: transference rat
-- statement:
--   The Short Vectors construction uses the transference rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TraceHermNondegenerate.lean#L57-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TraceHermNondegenerate.lean#L57-L139

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
open GlobalTheory.ShortVectors
variable {V : Type} [AddCommGroup V] [Module ℚ V]

theorem GlobalTheory.ShortVectors.transference_rat {M : ℕ} (b : Basis (Fin M) ℚ V)
    (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm) (hp : ∀ x, 0 ≤ B x x) (hn : B.Nondegenerate)
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ u, u ≠ 0 → (∀ j, ∃ k : ℤ, B u (b j) = k) → lam ^ 2 ≤ (B u u : ℝ)) :
    ∃ v : Fin M → V, (∀ i, v i ∈ span ℤ (Set.range b)) ∧ LinearIndependent ℚ v ∧
      ∀ i, (B (v i) (v i) : ℝ) ≤ ((M : ℝ) ^ 2 / lam) ^ 2 := by sorry
