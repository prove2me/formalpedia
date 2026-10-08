-- Prove2me | Theorems.Thm_LinParamBandits_UEGeneral_potential_sum_le_Vstar
-- name    : LinParamBandits.UEGeneral.potential_sum_le_Vstar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:16.073013+00:00
-- url     : https://prove2.me/theorems/b7c9a503-bbd2-4c76-9a17-f8018abed188
-- title:
--   Lemma B.10 — Σ ‖U_{t+1}‖²_{C_t} ≤ V*(ū²/λ₀, T − r)
-- statement:
--   Let $r \ge 2$, $\bar u, \lambda_0 > 0$, and let $b_1, \dots, b_r$ satisfy $\lambda_{\min}(\sum_{k=1}^r b_kb_k') \ge \lambda_0$. Let $U_1, U_2, \dots$ be arms with $U_k = b_k$ for $k \le r$ and $\|U_s\| \le \bar u$ for all $s$. Then for every $T \ge r+1$,
--   $$\sum_{t=r}^{T-1}\|U_{t+1}\|^2_{C_t} \le V^*\big(\bar u^2/\lambda_0,\ T - r\big),$$
--   where $V^*$ is the value of the optimization problem on p. 38 (in dimension $r$).
--
--   Together with Lemma B.11 this bounds the expectation in the regret decomposition, Lemma B.8, by $O(r\log T)$.
--
--   **Formalization Note** The paper states the lemma "under Assumption 1, with probability one" for the arms of the UE policy; its proof is pathwise and uses only $U_k = b_k$ for $k \le r$ and $\|U_s\| \le \bar u$. The Lean statement is made for **every** sequence `U : ℕ → Vec r` (entry `s` is $U_{s+1}$) with these two properties, which implies the almost sure statement for every UE run, and is stronger than printed. `potential U t` is $\|U_{t+1}\|^2_{C_t}$ with $C_t = (\sum_{s \le t}U_sU_s')^{-1}$, a genuine inverse for $t \ge r$ because $\lambda_{\min}(\sum_k b_kb_k') \ge \lambda_0 > 0$ (written as $x'(\sum_k b_kb_k')x \ge \lambda_0\|x\|^2$). No property of $z$ is involved.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma B.10, p. 38

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy
import Definitions.Def_LinParamBandits_UEGeneral_Vstar

namespace LinParamBandits.UEGeneral

open MeasureTheory ProbabilityTheory

/-- Lemma B.10 (p. 38): bound on the growth rate of `‖U_{t+1}‖²_{C_t}`, stated pathwise. -/
theorem potential_sum_le_Vstar {r : ℕ} (hr : 2 ≤ r) {b : Fin r → LinParamBandits.LowerBound.Vec r} {ubar lam0 : ℝ} (hubar : 0 < ubar)
    (hlam0 : 0 < lam0) (hb : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, inner ℝ (b k) x ^ 2)
    (U : ℕ → LinParamBandits.LowerBound.Vec r) (hU_init : ∀ (k : ℕ) (hk : k < r), U k = b ⟨k, hk⟩)
    (hU_norm : ∀ s, ‖U s‖ ≤ ubar)
    (T : ℕ) (hT : r + 1 ≤ T) :
    ∑ t ∈ Finset.Ico r T, potential U t ≤ Vstar r (ubar ^ 2 / lam0) (T - r) := by sorry

end LinParamBandits.UEGeneral
