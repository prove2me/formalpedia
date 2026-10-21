-- Prove2me | Theorems.Thm_IntertempDUI_Finite_theorem_B2_b
-- name    : IntertempDUI.Finite.theorem_B2_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:31.311645+00:00
-- url     : https://prove2.me/theorems/12e5a43a-8241-44e5-9433-23e982989bd1
-- title:
--   Theorem B2(b) — content-utility representation
-- statement:
--   On the finite horizon $[0,T]$, assume (R*) and (MinEqn). The preference structure satisfies (ISep), (LSep), (StEq), (C), (Dom), (CIP), and (TC) and ephemerality (Eph) if and only if it has a content-utility representation (B7) with a full-support content that is nonatomic. The representing content is unique on time spans, and $u$ is unique up to a positive affine transformation.
--
--   $$\text{seven axioms}\wedge(Eph)\Longleftrightarrow\exists(u,\mu)\text{ satisfying (B7)},$$
--
--   The statement is a step toward the finite-horizon characterization in Theorem 1.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, SSRN 3232014 (August 10, 2018), pp. 27–28, Theorem B2(b); https://ssrn.com/abstract=3232014

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Content

namespace IntertempDUI.Finite

/-- Theorem B2(b) and its uniqueness sentence, pp. 27–28, for [0,T]. -/
theorem theorem_B2_b {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (T : ℝ) (hT : 0 < T) (A : Set (Traj T X))
    (hconst : ∀ x : X, ContinuousMap.const (Time T) x ∈ A)
    (pref : Pref T X) (hstd : Standing A pref)
    (hR : RichnessStar A pref) (hM : MinEqn A pref) :
    ((ISep A pref ∧ LSep A pref ∧ StEq A pref ∧ CondC pref ∧
      Dom A pref ∧ CIP A pref ∧ TC A pref ∧ Eph A pref) ↔
      ∃ u : X → ℝ, ∃ μ : Set (Time T) → ℝ,
        IsContentUtilityRep A pref u μ ∧ FullSupport μ ∧ Nonatomic μ) ∧
    (∀ u μ u' μ', IsContentUtilityRep A pref u μ →
      IsContentUtilityRep A pref u' μ' →
      FullSupport μ → FullSupport μ' → Nonatomic μ → Nonatomic μ' →
      (∀ S, IsTimeSpan S → μ S = μ' S) ∧
      ∃ a b : ℝ, 0 < a ∧ ∀ x : X, u' x = a * u x + b) := by sorry

end IntertempDUI.Finite
