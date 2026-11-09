-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_theorem_4_1
-- name    : LowRandomnessDP.KNorm.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:21.694104+00:00
-- url     : https://prove2.me/theorems/d0f1a2fc-31f6-41dd-9f84-0a8cc18afcd0
-- title:
--   Theorem 4.1 — pure privacy, optimal norm error and logarithmic fair-bit cost
-- statement:
--   There exist absolute positive constants $C_e,C_b$ such that, for every $d\ge2$, every compact convex symmetric absorbing body $K\subseteq\mathbb R^d$, every $\varepsilon>0$, every dataset type $D$ with symmetric adjacency, and every real-valued vector query $f:D\to\mathbb R^d$ of $K$-norm sensitivity at most one, there is one family of almost-surely terminating fair-bit decision trees $T_x$ whose output laws are $\varepsilon$-differentially private and satisfy
--
--   $$\mathbb E[\|T_x-f(x)\|_K]\le C_e\frac d\varepsilon\quad\text{for every }x,\qquad
--   \sup_x\mathbb E[L_{T_x}]\le C_b\log_2 d.$$
--
--   The constants are chosen before all instance parameters. The same trees supply privacy, error and operational randomness. No partition, entropy bound or sampler is assumed. No efficiency or rational-output restriction is imposed.
--
--   Differences from the source:
--   - encoding: real vectors and their K-norm → Fin d → ℝ with the Minkowski gauge of the exact compact convex symmetric absorbing disk; reason: coordinate encoding preserves all real vectors and all source norms; compactness excludes nontrivial linear subspaces
--   - generalization: finite datasets X* → an arbitrary dataset type D with a symmetric adjacency relation; reason: specializes to D=List X with every source neighboring relation; no input measurability is imposed
--   - encoding: expected error and randomness complexity O(log d) → extended nonnegative expectations and a supremum of expected prefix-free leaf depths bounded by Cb log₂ d; reason: mass-one DDG trees implement actual independent fair-bit consumption; logarithm base changes only the uniform absolute O constant
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf, Theorem 4.1, PDF page 15 / printed page 13

import Definitions.Def_LowRandomnessDP_KNorm_Sampling

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace LowRandomnessDP.KNorm

theorem theorem_4_1 :
    ∃ Ce Cb : ℝ, 0 < Ce ∧ 0 < Cb ∧
      ∀ (d : ℕ), 2 ≤ d → ∀ K : Set (Vec d), IsBody K →
      ∀ ε : ℝ, 0 < ε → ∀ (D : Type) (adj : D → D → Prop), Std.Symm adj →
      ∀ f : D → Vec d, SensitivityOne adj K f →
        ∃ T : D → DDG (Vec d),
          PureDP adj ε (fun x => (T x).law.toMeasure) ∧
          (∀ x, expectedError K (T x) (f x) ≤ ENNReal.ofReal (Ce * d / ε)) ∧
          randomnessComplexity T ≤ ENNReal.ofReal (Cb * Real.logb 2 d) := by sorry

end LowRandomnessDP.KNorm
