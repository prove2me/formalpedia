-- Prove2me | Theorems.Thm_MDPFinance_InfiniteHorizonApplications_theorem_7_6_6
-- name    : MDPFinance.InfiniteHorizonApplications.theorem_7_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:01:11.94438+00:00
-- url     : https://prove2.me/theorems/6d1663a2-25f6-44f5-9dff-fa9ee77e11ae
-- title:
--   Theorem 7.6.6 — the Gittins index as a supremum over stopping times
-- statement:
--   The Gittins index $I(m_0,n_0)$, defined implicitly via a fixed-point equation, has an equivalent
--   explicit representation as the supremum, over every possible stopping time $\tau$, of the
--   discounted average reward collected before stopping — and this supremum is actually *attained*,
--   at the specific stopping time $\tau^*$ that stops the first time the current index drops to or
--   below the starting index. This is what makes the index computable in practice and is the key
--   technical fact Corollary 7.6.8's indifference property is built from.
--
--   **Moderation note.** The draft's expectations `EReward`/`EDiscount` were unconstrained functionals (any pair with positive denominators), so the identity was refutable, and its $\tau^*$ included $n=0$ (always stopping at once) while also being assumed $\ge 1$, making the statement vacuous. Both are now defined from the arm's predictive law (`EStop`, `tauStar` with $n\ge 1$), and $\tau^*$ is asserted to be a stopping time $\ge 1$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 231, Theorem 7.6.6

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Bandit

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- Theorem 7.6.6 (Bäuerle–Rieder, p. 231, PDF 242). Let `i_0 = (m_0,n_0) \in \mathbb N_0^2` be
fixed, `r(m,n) := p(m,n)` and `(X_k)` the state process of the `K`-stopping problem started at
`i_0` under repeated pulling. Then `I(m_0,n_0) = \mathbb E_{i_0}[\sum_{k=0}^{\tau^*-1}\beta^kr(X_k)]
/((1-\beta)\mathbb E_{i_0}[\sum_{k=0}^{\tau^*-1}\beta^k]) = \sup_{\tau\ge1} \mathbb
E_{i_0}[\sum_{k=0}^{\tau-1}\beta^kr(X_k)]/((1-\beta)\mathbb E_{i_0}[\sum_{k=0}^{\tau-1}\beta^k])`
where `\tau^* := \inf\{n\in\mathbb N\mid I(X_n)\le I(i_0)\}` (`n ≥ 1`) and the supremum is over
all stopping times `τ ≥ 1`. The expectations are `EStop` (finite sums over outcome prefixes
weighted by the predictive law, discounted); `τ^*` is `tauStar`, and is asserted to be a
stopping time with `τ^* ≥ 1`. -/
theorem theorem_7_6_6 {β : ℝ} (KS : KStoppingValue β pMN) (m0 n0 : ℕ) :
    IsStoppingTime (tauStar KS (m0, n0)) ∧ IsPositiveStoppingTime (tauStar KS (m0, n0)) ∧
      GittinsIndex KS (m0, n0) =
        EStop β pMN (tauStar KS (m0, n0)) (m0, n0) /
          ((1 - β) * EStop β (fun _ => 1) (tauStar KS (m0, n0)) (m0, n0)) ∧
      GittinsIndex KS (m0, n0) =
        ⨆ τ ∈ {τ : (ℕ → ℕ × ℕ) → ℕ∞ | IsStoppingTime τ ∧ IsPositiveStoppingTime τ},
          EStop β pMN τ (m0, n0) / ((1 - β) * EStop β (fun _ => 1) τ (m0, n0)) := by sorry

end MDPFinance.InfiniteHorizonApplications
