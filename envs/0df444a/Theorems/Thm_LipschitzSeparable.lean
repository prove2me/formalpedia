-- Prove2me | Theorems.Thm_LipschitzSeparable
-- name    : LipschitzSeparable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:54:30.48732+00:00
-- url     : https://prove2.me/theorems/1c1db431-3714-4b52-a0c0-cfeb132076dd
-- title:
--   Lipschitz Separable: Lipschitz Separable
-- statement:
--   Paper Lemma A.1 (paper.tex 1602), in the tablet's bound idiom. There is a countable family
--   `P : ℕ → E → ℝ` of bounded Lipschitz functions, with named bound/Lipschitz-constant fields `B`, `L`,
--   such that every Lipschitz `π : E → ℝ` with Lipschitz bound `K` is the pointwise limit along some
--   subsequence `P ∘ φ` of members that are themselves `K`-Lipschitz (never exceeding `π`'s own bound
--   `K`), and any bound `M` on `π` is inherited exactly by every member of the subsequence. This is a
--   deliberate weakening of the paper's lemma: it drops the paper's two convergence-of-constants
--   clauses `Lip(π_{n_k}) → Lip(π)` and `‖π_{n_k}‖_∞ → ‖π‖_∞`, which concern the *optimal* Lipschitz
--   constant and sup-norm of `π` — notions this tablet does not have, since `Form1` carries `fLip`/
--   `piLip` only as Lipschitz-with *bounds*, not as optimal constants. See the `.tex` for the
--   justification that no downstream consumer needs those two clauses.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/LipschitzSeparable.lean#L18-L361
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/LipschitzSeparable.lean#L18-L361

import Definitions.Def_Tablet_ConeInterpolation
import Definitions.Def_Tablet_RationalCompatibleValues
import Definitions.Def_Tablet_LipschitzSeparable
import Theorems.Thm_ConeInterpolation
import Theorems.Thm_RationalCompatibleValues

set_option autoImplicit false
open scoped NNReal
open Filter Topology

theorem LipschitzSeparable {E : Type*} [MetricSpace E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] :
    ∃ (P : ℕ → E → ℝ) (B L : ℕ → ℝ≥0),
      (∀ n, (∀ x, |P n x| ≤ (B n : ℝ)) ∧ LipschitzWith (L n) (P n)) ∧
      ∀ (π : E → ℝ) (K : ℝ≥0), LipschitzWith K π →
        ∃ φ : ℕ → ℕ,
          (∀ k, LipschitzWith K (P (φ k))) ∧
          (∀ x, Tendsto (fun k => P (φ k) x) atTop (nhds (π x))) ∧
          (∀ M : ℝ≥0, (∀ x, |π x| ≤ (M : ℝ)) → ∀ k, ∀ x, |P (φ k) x| ≤ (M : ℝ)) := by sorry
