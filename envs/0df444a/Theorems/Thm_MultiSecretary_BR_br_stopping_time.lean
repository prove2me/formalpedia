-- Prove2me | Theorems.Thm_MultiSecretary_BR_br_stopping_time
-- name    : MultiSecretary.BR.br_stopping_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:18:49.012546+00:00
-- url     : https://prove2.me/theorems/39cccaff-c1b8-40c8-9cca-298d00ba11c4
-- title:
--   Theorem 2 — BR stopping time: $\mathbb E[\tau]\ge n-M$ uniformly over $(n,k)\in\mathcal T$
-- statement:
--   Let $\epsilon>0$ and $0<\delta<\epsilon$. There is a constant $M$ such that for every multi-secretary instance with $\tfrac12\min\{f_m,\dots,f_1\}=\epsilon$ and every $(n,k)\in\mathcal T$, the stopping time $\tau$ of (20) for the Budget-Ratio policy satisfies
--   $$\mathbb E[\tau]\ge n-M.$$
--
--   The budget ratio of BR stays near the threshold it is attracted to until a bounded expected number of periods before the horizon. This is condition (iv) of Proposition 2 for the BR policy.
--
--   **Formalization Note** The constant is chosen after $\epsilon$ and $\delta$ and before the number of ability levels, the distribution, $n$ and $k$. The page writes $M\equiv M(\epsilon)$; but $\tau$ depends on the $\delta$ fixed on p. 13, and $\tau\le n-2\delta^{-1}$ roughly whenever $\tau_0<n-2\delta^{-1}-1$, so no $\delta$-free constant exists. $\delta$ is therefore quantified before $M$.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Theorem 2, p. 16; τ₀ on p. 13, τ in eq. (20), p. 15

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model
import Definitions.Def_MultiSecretary_BR_Policy

namespace MultiSecretary.BR

/-- Theorem 2 (BR stopping time), p. 16. Let `ϵ = ½ min_j f_j` and fix `0 < δ < ϵ` (p. 13). There is
a constant `M` such that for all `(n, k) ∈ T` the stopping time `τ` of (20) satisfies
`E[τ] ≥ n − M`. The constant is chosen after `ϵ` and `δ` and before the support size, the
distribution, `n` and `k` (the page writes `M ≡ M(ϵ)`; `τ` depends on `δ`, and so must `M`). -/
theorem br_stopping_time (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ < ε) :
    ∃ M : ℝ, ∀ (m : ℕ) (I : Instance m), I.eps = ε → ∀ n k : ℕ, k ≤ n →
      (n : ℝ) - M ≤ I.E (fun x : Fin n → Fin m => (I.tau δ n k x : ℝ)) := by sorry

end MultiSecretary.BR
