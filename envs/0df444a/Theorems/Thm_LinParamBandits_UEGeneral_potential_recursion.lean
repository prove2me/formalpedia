-- Prove2me | Theorems.Thm_LinParamBandits_UEGeneral_potential_recursion
-- name    : LinParamBandits.UEGeneral.potential_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:11.497437+00:00
-- url     : https://prove2.me/theorems/8526ca1a-85db-4fe0-9a70-1e187df00fda
-- title:
--   Lemma B.9 — large past regrets imply small current regret
-- statement:
--   Let $r \ge 2$, $\bar u, \lambda_0 > 0$, and let $b_1, \dots, b_r$ satisfy $\lambda_{\min}(\sum_{k=1}^r b_kb_k') \ge \lambda_0$. Let $U_1, U_2, \dots$ be arms with $U_k = b_k$ for $k \le r$ and $\|U_s\| \le \bar u$ for all $s$, and let $C_t = (\sum_{s=1}^t U_sU_s')^{-1}$. Then for all $t \ge r$,
--   $$0 \le \|U_{t+1}\|^2_{C_t} \le \frac{\bar u^2}{\lambda_0} \qquad\text{and}\qquad \|U_{t+1}\|^2_{C_t} \le \frac{\{(\bar u^2/\lambda_0)\cdot(t+1)\}^r}{\prod_{s=r}^{t-1}\big(1 + \|U_{s+1}\|^2_{C_s}\big)},$$
--   the empty product (at $t = r$) being $1$.
--
--   If the past weighted norms are large, the current one is small; this recursion is what bounds their sum through the problem $V^*$ (Lemma B.10).
--
--   **Formalization Note** The paper states the lemma "under Assumption 1, with probability one" for the arms of the UE policy; its proof is pathwise and uses only $U_k = b_k$ for $k \le r$ and $\|U_s\| \le \bar u$. The Lean statement is made for **every** sequence `U : ℕ → Vec r` (entry `s` is $U_{s+1}$) with these two properties, which implies the almost sure statement for every UE run, and is stronger than printed. `potential U t` is $\|U_{t+1}\|^2_{C_t}$ with $C_t = (\sum_{s \le t}U_sU_s')^{-1}$, a genuine inverse for $t \ge r$ because $\lambda_{\min}(\sum_k b_kb_k') \ge \lambda_0 > 0$ (written as $x'(\sum_k b_kb_k')x \ge \lambda_0\|x\|^2$). No property of $z$ is involved.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma B.9, p. 37 (proof pp. 37–38)

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy

namespace LinParamBandits.UEGeneral

open MeasureTheory ProbabilityTheory

/-- Lemma B.9 (p. 37): large past regrets imply small current regret, stated pathwise for every
arm sequence that starts with `b_1, …, b_r` and stays in the ball of radius `ū`. -/
theorem potential_recursion {r : ℕ} (hr : 2 ≤ r) {b : Fin r → LinParamBandits.LowerBound.Vec r} {ubar lam0 : ℝ} (hubar : 0 < ubar)
    (hlam0 : 0 < lam0) (hb : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, inner ℝ (b k) x ^ 2)
    (U : ℕ → LinParamBandits.LowerBound.Vec r) (hU_init : ∀ (k : ℕ) (hk : k < r), U k = b ⟨k, hk⟩)
    (hU_norm : ∀ s, ‖U s‖ ≤ ubar)
    (t : ℕ) (ht : r ≤ t) :
    0 ≤ potential U t ∧ potential U t ≤ ubar ^ 2 / lam0 ∧
    potential U t ≤
      (ubar ^ 2 / lam0 * ((t : ℝ) + 1)) ^ r / ∏ s ∈ Finset.Ico r t, (1 + potential U s) := by sorry

end LinParamBandits.UEGeneral
