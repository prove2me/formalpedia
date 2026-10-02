-- Prove2me | Theorems.Thm_MDPFinance_InfiniteHorizonApplications_theorem_7_6_10
-- name    : MDPFinance.InfiniteHorizonApplications.theorem_7_6_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:01:22.911707+00:00
-- url     : https://prove2.me/theorems/edaff850-53fd-4241-96a7-4787803b92bf
-- title:
--   Theorem 7.6.10 — the Gittins index policy is optimal for the two-arm bandit
-- statement:
--   This is the section's capstone: always pulling the arm with the higher Gittins index is optimal
--   for the full infinite-horizon two-armed bandit. What makes this remarkable, and is the theorem's
--   real content, is *how* each index is computed: $I(m_a,n_a)$ depends only on arm $a$'s own
--   observed history, never on the other arm's state — so instead of solving one optimization problem
--   over the full four-dimensional joint state space, the decision maker solves two independent,
--   two-dimensional single-arm problems and simply compares two numbers. This dimensionality
--   reduction, not merely the existence of an optimal policy, is what the theorem is stated to
--   demonstrate, and this formalization keeps the two single-arm index computations manifestly
--   separate (via `GittinsIndex KS x.1` and `GittinsIndex KS x.2`, the *same* single-arm
--   `KStoppingValue`) rather than folding them into one joint index function that happened to equal
--   this — which would obscure exactly this point. The proof route here (via the `K`-stopping
--   problem's explicit fixed-point characterization) is genuinely different from the platform's
--   existing Gittins-index theorems (`BanditAlgorithm.gittins_index_theorem` and related, built via
--   Whittle's retirement/charge-accounting construction) — checked directly and confirmed to define
--   the index differently enough (retirement value vs. this book's $\min\{K \mid J(\cdot;K)=K\}$) that
--   this mission drafts its own theorems rather than reference that construction.
--
--   **Moderation note.** Optimality of the index policy is stated as $J_{f^*}=J_\infty$ (value of the stationary policy, `banditVpi`), together with the draft's maximizer property.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 234, Theorem 7.6.10

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Bandit

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- **Theorem 7.6.10** (Bäuerle–Rieder, p. 234, PDF 245 — corrected from `BRIEF.md`'s "p. 235";
the printed-page footer at PDF 245 reads `234`, the goal theorem of this mission). The
stationary Index-policy `(f^*,f^*,\dots)` is optimal for the infinite horizon bandit problem
where for `x = (m_1,n_1,m_2,n_2)`: `f^*(x) := 2` if `I(m_2,n_2) \ge I(m_1,n_1)`, `1` if
`I(m_2,n_2) < I(m_1,n_1)`. The index `I(m_a,n_a)` used to decide between the arms is computed
from *arm `a`'s own state alone* (`GittinsIndex KS x.1`/`GittinsIndex KS x.2`, the *same*
single-arm `KStoppingValue KS`, never a function of the *other* arm's state) — this is the
theorem's actual content (the book's own remark: "we can compute for each arm separately its own
index … the dimension of the state space … is reduced dramatically"), not incidental to how the
statement happens to be written. Optimality is stated as `J_{f^*} = J_∞` (the value
`sup_n V_n^{f^*}` of the stationary index policy equals the bandit's value function), together
with `f^*` being a maximizer of `J_∞`. -/
theorem theorem_7_6_10 {β : ℝ} (KS : KStoppingValue β pMN) (BV : BanditValue β)
    (fstar : BanditState2 → Fin 2)
    (hfstar : ∀ x : BanditState2, fstar x = if GittinsIndex KS x.1 ≤ GittinsIndex KS x.2
      then 1 else 0) :
    (∀ x, (⨆ n, banditVpi β fstar n x) = BV.Jinf x) ∧
      ∀ x, (if fstar x = 0 then paBandit 0 x + β * QaBandit 0 BV.Jinf x
        else paBandit 1 x + β * QaBandit 1 BV.Jinf x) = BV.Jinf x := by sorry

end MDPFinance.InfiniteHorizonApplications
