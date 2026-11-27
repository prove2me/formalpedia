-- Prove2me | Theorems.Thm_HLambdaG_Main_Supplement_theorem_8_refuted
-- name    : HLambdaG.Main.Supplement.theorem_8_refuted
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T01:07:00.244803+00:00
-- url     : https://prove2.me/theorems/b764a00b-9946-4b52-8863-ab9b6bff25bb
-- title:
--   Theorem 8, p. 644 — corrected disposition: explicit refutation of the printed FCLT and (30)
-- statement:
--   In the standard framework of §1.3 take $\lambda=g=h=1$, $T_k=k$, $S_k=\sqrt k+1$, and the nonnegative integrable rate $f_k(v)=2k1_{[k+\sqrt k,k+\sqrt k+1]}(v)$. This satisfies (33) and $S_k/T_k\to0$, the complete delay assumption (34). Its integrated inputs are $F_k(t)=2k\min(1,(t-k-\sqrt k)^+)$, with $F_k(\infty)=2k$. Let $G,H$ be the averages (1), and $T_1(s)=\lfloor s\rfloor$. Uniformly on bounded time intervals, the printed scaling (27) gives
--   $$
--   G_n\to0,\qquad T_n^1\to0,\qquad H_n\to-2\sqrt t.
--   $$
--   Theorem 8 would require $H(t)=G(t)-T(t)=0$ by (30), contradicting the actual limit at time one.
--
--   **Formalization Note** The item is an explicit refutation of the printed theorem, not a narrowed transfer theorem. Lean records nonnegativity, integrability, support, the integral formula, all customer totals, (34), compact convergence and $-2\ne0$. The formulas imply finite marginal limits: at a fixed $t$ only customers $k\le t$ contribute. These deterministic right-continuous paths have left limits, and the limits are continuous, so compact convergence establishes the stated FCLT antecedent on a singleton probability space. No arbitrary second time change is introduced. $G,H$ retain their printed meaning as averages. The notation omission '$P(S\in C)$' does not affect this witness, whose limit paths are continuous with probability one.
--
--   Differences from the source:
--
--   - correction: Theorem 8 asserts FCLT transfer and the limit identities (30) → an explicit deterministic refutation of the printed result, using the averages (1) literally in (27); reason: with T_k=k, S_k=√k+1 and f_k=2k on [k+√k,k+√k+1], (33),(34) hold, G_n,T¹_n→0, but H_n→−2√t; (30) requires H=0
-- source:
--   Glynn and Whitt, Oper. Res. 37 (1989), p. 644, Theorem 8 and displays (27)–(30), (33)–(34)

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_FCLTExamples

open scoped NNReal

namespace HLambdaG.Main.Supplement

open Filter Topology MeasureTheory

/-- Refutation of Theorem 8 under its printed assumptions (33),(34), with λ = g = h = 1.
T_k = k, S_k = √k + 1, f_k = 2k on [k + √k, k + √k + 1], zero elsewhere.
Every f_k is nonnegative and integrable, and S_k/T_k → 0. The source's AVERAGES
(1), used literally in (27), give G_n → 0, T¹_n → 0, but H_n → -2√t uniformly on
compact time intervals. Thus the claimed relation (30), H = G - hT = 0, is false.
The deterministic continuous limit also witnesses failure of the claimed limit law. -/
theorem theorem_8_refuted :
    (∀ k : ℕ, (∀ t : ℝ, 0 ≤ delayedRate k t) ∧
      Integrable (delayedRate k) ∧
      (∀ t : ℝ, t ∉ Set.Icc (k : ℝ) ((k : ℝ) + (Real.sqrt k + 1)) →
        delayedRate k t = 0) ∧
      (∀ t : ℝ≥0, delayedF k t = ∫ v in Set.Icc (0 : ℝ) t, delayedRate k v) ∧
      Tendsto (delayedF k) atTop (𝓝 (2 * k : ℝ))) ∧
    Tendsto (fun k : ℕ => (Real.sqrt k + 1) / (k : ℝ)) atTop (𝓝 0) ∧
    CompactConvergence (diffusion delayedG) (fun _ => 0) ∧
    CompactConvergence (diffusion integerT) (fun _ => 0) ∧
    CompactConvergence (diffusion delayedH) (fun t => -2 * Real.sqrt t) ∧
    (-2 * Real.sqrt (1 : ℝ) ≠ (0 : ℝ) - 1 * 0) := by sorry

end HLambdaG.Main.Supplement
