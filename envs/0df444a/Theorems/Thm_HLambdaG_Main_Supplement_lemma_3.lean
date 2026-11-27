-- Prove2me | Theorems.Thm_HLambdaG_Main_Supplement_lemma_3
-- name    : HLambdaG.Main.Supplement.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T01:03:13.636632+00:00
-- url     : https://prove2.me/theorems/d5fd59d5-7294-4053-8026-53e40e696a17
-- title:
--   Lemma 3, p. 640 — S_n/T_n → 0 implies U_n/T_n → 0 for the running maximum U_n of (19)
-- statement:
--   Let $0=T_0\le T_1\le T_2\le\cdots$ be the epochs of §1.1, with $T_n\to\infty$, and let $\{S_k\}$ be a nonnegative finite sequence. With the running maximum
--   $$
--   U_n=\max\{S_k:\ 1\le k\le n\} \tag{19}
--   $$
--   the lemma states
--   $$
--   \frac{S_n}{T_n}\to0\quad\Longrightarrow\quad\frac{U_n}{T_n}\to0\qquad(n\to\infty).
--   $$
--
--   This is the step that lets Theorem 3 replace the individual delays $S_k$ in (18) by the monotone sequence $U_n$, which defines the time change $T_2(s)=T_{[s]}+U_{[s]}$.
--
--   **Formalization Note** $U_0=0$ is the empty maximum. Ratios use Lean's real division, which gives $0$ when $T_n=0$. Since $T_n\to\infty$, only finitely many $n$ are affected, and the limits are along $n\to\infty$.
--
--   Differences from the source:
--
--   - encoding: S_n/T_n and U_n/T_n for all n → real division, which is 0 for the finitely many n with T_n = 0; reason: Lean convention; T_n → ∞, so the limit statements are unchanged
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 640, Lemma 3 and display (19); https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_Discrete

open scoped NNReal

namespace HLambdaG.Main.Supplement

open Filter Topology

/-- Lemma 3, p. 640: for the epochs of §1.1 and a nonnegative finite sequence `S`,
`S_n / T_n → 0` implies `U_n / T_n → 0`, where `U_n = max {S_k : 1 ≤ k ≤ n}`. -/
theorem lemma_3 (T : ℕ → ℝ≥0) (hT0 : T 0 = 0) (hmono : Monotone T)
    (htend : Tendsto T atTop atTop) (S : ℕ → ℝ≥0)
    (hS : Tendsto (fun n : ℕ => (S n : ℝ) / (T n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (U S n : ℝ) / (T n : ℝ)) atTop (𝓝 0) := by sorry

end HLambdaG.Main.Supplement
