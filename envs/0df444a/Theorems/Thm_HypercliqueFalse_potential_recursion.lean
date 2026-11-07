-- Prove2me | Theorems.Thm_HypercliqueFalse_potential_recursion
-- name    : HypercliqueFalse.potential_recursion
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:29:57.084864+00:00
-- url     : https://prove2.me/theorems/775720d5-7f0d-4fa7-a0b9-97c515a46eb8
-- title:
--   Proof of Theorem 2.1 ($h=3$) — the potential of the recursion and $\epsilon = \log_q(1/\rho)$
-- statement:
--   Let $q \ge 2$ be an integer, $L \in \mathbb N$, $\delta, \Phi \in \mathbb R$, and
--   $$
--   \rho = q^{-\delta} + (1 - 1/q)\,2^{-\delta}.
--   $$
--   Then, with $n = q^{2L}$:
--
--   1. the children of a node with potential $\Phi$ have total potential $q\cdot q^{1-\delta}\Phi + \binom q2\cdot 2^{1-\delta}\Phi = \rho q^2\Phi$;
--   2. $\rho \le 2^{-\delta}\big(1 + (2/q)^{\delta}\big)$;
--   3. the leaves have total potential $(\rho q^2)^{2L} = n^2\rho^{2L}$;
--   4. $n^2\rho^{2L} = n^{2 - \log_q(1/\rho)}$, so $n^4\rho^{2L} = n^{4-\epsilon}$ for $\epsilon = \log_q(1/\rho)$;
--   5. $\epsilon = \log_q(1/\rho) \ge \dfrac{\delta - \log_2(1 + (2/q)^\delta)}{\log_2 q}$.
--
--   The potential of a node of size $(N, M, a, b, c)$ is $(abc)^{1-\delta}$; this calculation is reused in the proof of Theorem 2.1 for every $h$ ("by the same calculation as before").
--
--   Differences from the source:
--   - generalization: q a sufficiently large integer constant, δ ∈ (0, 1) (δ = 0.02, resp. ε²_{h−1}/8) → every integer q ≥ 2 and every real δ, Φ; reason: the identities and bounds hold there; specializes to the paper's q and δ
--   - encoding: L = log_q(n)/2, n padded to q^{2L} → n written as q^{2L}; reason: same quantity
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof of Theorem 2.1 for h = 3, p.9; reused in the proof of Theorem 2.1, p.13

import Mathlib

set_option autoImplicit false

namespace HypercliqueFalse

/-- **The potential calculation of the recursion.** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof of Theorem 2.1
for h = 3, p.9 (reused in the proof of Theorem 2.1, p.13: "by the same calculation as before"):
"Define the potential of a node of size (N, M, a, b, c) as (abc)^{1−δ}. The root has potential 1, and
the children of a node with potential Φ have total potential q · q^{1−δ}Φ + (q choose 2) · 2^{1−δ}Φ;
this becomes ρq²Φ for ρ = q^{−δ} + (1 − 1/q) 2^{−δ} ≤ 2^{−δ}(1 + (2/q)^δ). Hence, the leaves have
total potential (ρq²)^{2L} = n²ρ^{2L}. … Recalling that L = log_q(n)/2, this becomes O(n^{4−ϵ}) for
ϵ = log_q(1/ρ) ≥ (δ − log₂(1 + (2/q)^δ)) / log₂ q."

The clauses: the children's total potential; the bound on `ρ`; the leaves' total potential for
`n = q^{2L}`; `n²ρ^{2L} = n^{2−log_q(1/ρ)}` (the step from `n⁴ρ^{2L}` to `n^{4−ϵ}`); the lower bound
on `ϵ = log_q(1/ρ)`. -/
theorem potential_recursion (q L : ℕ) (hq : 2 ≤ q) (δ ρ Φ : ℝ)
    (hρ : ρ = (q : ℝ) ^ (-δ) + (1 - 1 / (q : ℝ)) * (2 : ℝ) ^ (-δ)) :
    (q : ℝ) * ((q : ℝ) ^ (1 - δ) * Φ) + (q.choose 2 : ℝ) * ((2 : ℝ) ^ (1 - δ) * Φ) =
        ρ * (q : ℝ) ^ 2 * Φ ∧
      ρ ≤ (2 : ℝ) ^ (-δ) * (1 + (2 / (q : ℝ)) ^ δ) ∧
      (ρ * (q : ℝ) ^ 2) ^ (2 * L) = ((q : ℝ) ^ (2 * L)) ^ 2 * ρ ^ (2 * L) ∧
      ((q : ℝ) ^ (2 * L)) ^ 2 * ρ ^ (2 * L) = ((q : ℝ) ^ (2 * L)) ^ (2 - Real.logb q (1 / ρ)) ∧
      (δ - Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ)) / Real.logb 2 q ≤ Real.logb q (1 / ρ) := by sorry

end HypercliqueFalse
