-- Prove2me | Theorems.Thm_KalaiVempala_Lazy_fll_update_bound
-- name    : KalaiVempala.Lazy.fll_update_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:26.264191+00:00
-- url     : https://prove2.me/theorems/eb59cc4d-559e-49c4-aa0c-bb59bd8c7a22
-- title:
--   Proof of Lemma 1.2 (FLL case), p. 303 — P(g_{t−1} ≠ g_t) ≤ ε|s_t|₁
-- statement:
--   **FLL rarely moves.** Let $\varepsilon > 0$, let $p$ be uniform on $[0, 1/\varepsilon]^n$, and let $g(x, p)$ be the grid point of FLL($\varepsilon$), the unique point of $p + \tfrac1\varepsilon\mathbb Z^n$ in $x + [0, 1/\varepsilon)^n$. For all $x, v \in \mathbb R^n$,
--
--   $$\Pr_{p}\big[\, g(x, p) \ne g(x + v, p) \,\big] \;\le\; \varepsilon |v|_1 .$$
--
--   With $x = s_{1:t-1}$ and $v = s_t$, so that $x + v = s_{1:t}$, this is the paper's bound $\Pr[g_{t-1} \ne g_t] \le \varepsilon |s_t|_1$: FLL($\varepsilon$) has to change its decision (and call the oracle) on period $t$ with probability at most $\varepsilon|s_t|_1$.
--
--   **Formalization Note** The probability is the `perturbLaw n ε`-measure of the event, in `ℝ≥0∞`. No bound on $v$ is assumed; when $\varepsilon |v|_1 \ge 1$ the claim is trivial.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 303, proof of Lemma 1.2 (FLL case), last paragraph

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Lazy_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Lazy

theorem fll_update_bound {n : ℕ} (ε : ℝ) (hε : 0 < ε) (x v : Fin n → ℝ) :
    perturbLaw n ε {p | fllGridPoint ε x p ≠ fllGridPoint ε (x + v) p} ≤
      ENNReal.ofReal (ε * ∑ i, |v i|) := by sorry

end KalaiVempala.Lazy
