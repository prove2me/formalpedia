-- Prove2me | Theorems.Thm_MultiSecretary_BR_uniformly_bounded_regret
-- name    : MultiSecretary.BR.uniformly_bounded_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:19:16.180607+00:00
-- url     : https://prove2.me/theorems/1db0e56b-4e3d-4c74-996b-3a2a63cce875
-- title:
--   Theorem 1 — the Budget-Ratio policy has regret at most $a_1M(\epsilon)$, uniformly in $(n,k)\in\mathcal T$
-- statement:
--   Let $\epsilon>0$. There is a constant $M$ such that for every multi-secretary instance (abilities $a_1>\dots>a_m>0$, masses $f_j>0$ summing to one) with $\tfrac12\min\{f_m,\dots,f_1\}=\epsilon$, and for every $(n,k)\in\mathcal T$, the Budget-Ratio policy $\mathrm{br}$ is a feasible online policy, $\mathrm{br}\in\Pi(n,k)$, and
--   $$V^*_{\mathrm{off}}(n,k)-V^*_{\mathrm{on}}(n,k)\le V^*_{\mathrm{off}}(n,k)-V^{\mathrm{br}}_{\mathrm{on}}(n,k)\le a_1M.$$
--
--   The regret of the optimal online policy, and of the simple Budget-Ratio policy, against the offline benchmark is bounded by a constant that depends only on $\epsilon$: it does not grow with the number of candidates $n$ or the budget $k$.
--
--   **Formalization Note** The constant $M$ is chosen after $\epsilon$ and before the number of ability levels $m$, the distribution, $n$ and $k$ (the page's $M\equiv M(\epsilon)$). Since $2\epsilon m\le\sum_jf_j=1$, $m$ is bounded in terms of $\epsilon$. The page says "there exists a policy br"; the statement names the paper's Budget-Ratio policy of Sec. 4, the policy the paper constructs, which is the stronger form. $V^*_{\mathrm{on}}$ is the maximum over deterministic feasible online policies (see the model definition), which does not weaken the bound.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Theorem 1, p. 5, first display

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model
import Definitions.Def_MultiSecretary_BR_Policy

namespace MultiSecretary.BR

/-- Theorem 1 (The regret of online feasible policies), p. 5, first display. Let
`ϵ = ½ min{f_m, …, f_1}`. Then the Budget-Ratio policy `br` (Sec. 4) belongs to `Π(n, k)` and there
is a constant `M ≡ M(ϵ)` such that
`V*_off(n, k) − V*_on(n, k) ≤ V*_off(n, k) − V^br_on(n, k) ≤ a_1 M` for all `(n, k) ∈ T`.
`M` is chosen after `ϵ` and before the number `m` of ability levels, the distribution `(a, f)`, `n`
and `k`. -/
theorem uniformly_bounded_regret (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ (m : ℕ) (I : Instance m), I.eps = ε → ∀ n k : ℕ, k ≤ n →
      I.brPolicy n k ∈ policies n m k ∧
      I.Voff n k - I.Von n k ≤ I.Voff n k - I.value (I.brPolicy n k) ∧
      I.Voff n k - I.value (I.brPolicy n k) ≤ I.a I.top * M := by sorry

end MultiSecretary.BR
