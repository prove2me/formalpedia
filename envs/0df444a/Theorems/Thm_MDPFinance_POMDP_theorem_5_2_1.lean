-- Prove2me | Theorems.Thm_MDPFinance_POMDP_theorem_5_2_1
-- name    : MDPFinance.POMDP.theorem_5_2_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:15:01.699276+00:00
-- url     : https://prove2.me/theorems/a0f454f3-f733-40a2-90b5-8e04c63812e8
-- title:
--   Theorem 5.2.1 — the filter is the true conditional law of the hidden state
-- statement:
--   For all $\pi\in\Pi_N$ and $C\in\mathcal{B}(E_Y)$: $\mu_n(C\mid X_0,A_0,\dots,
--   X_n) = \mathbb{P}_x^\pi(Y_n\in C\mid X_0,A_0,\dots,X_n)$ — formalized via the book's own
--   Equation (5.5), the test-function identity it is proved and used through:
--   $$\mathbb{E}_x^\pi[v(X_0,A_0,\dots,X_n,Y_n)] = \mathbb{E}_x^\pi[v'(X_0,A_0,\dots,X_n)],
--   \qquad v'(h_n):=\int v(h_n,y_n)\,\mu_n(dy_n\mid h_n).$$
--
--   This confirms that the recursively-computable $\mu_n$ (Eq. (5.3)-(5.4)) is not merely *a*
--   useful statistic, but genuinely *the* Bayesian posterior of the hidden state given everything
--   observed — the fact that licenses treating $(X_n,\mu_n)$ as a sufficient statistic for
--   optimization, which §5.3 exploits.
--
--   **Formalization Note.** Stated via Eq. (5.5)'s test-function identity rather than Mathlib's
--   conditional-expectation-w.r.t.-a-sub-$\sigma$-algebra machinery: the two are equivalent by the
--   standard characterization of conditional expectation via bounded test functions, and the
--   test-function form is exactly what the book's own proof (and Theorem 5.3.2's later use of the
--   analogous Eq. (5.8)) operates on directly, avoiding the need to separately construct a canonical
--   trajectory sample space and a sub-$\sigma$-algebra on it.
--
--   **Moderation note.** The test function is bounded (`hv_bdd`), so that every expectation in (5.5) exists, as the book's proviso requires; the conditional-distribution statement is the case $v=\mathbf 1_{B\times C}$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 152, PDF 165, Theorem 5.2.1 (via Equation (5.5))

import Mathlib
import Definitions.Def_MDPFinance_POMDP_Model
import Definitions.Def_MDPFinance_POMDP_Policy
import Definitions.Def_MDPFinance_POMDP_Objective
import Definitions.Def_MDPFinance_POMDP_FilterData

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDP

/-- Theorem 5.2.1 (Bäuerle–Rieder, p. 152, PDF 165), via the book's own Equation (5.5): for every
`π ∈ Π_N`, `n ≤ N`, and every (bounded, measurable) test function `v` of the observable history
and the current unobservable state, `𝔼^π_x[v(X_0,A_0,…,X_n,Y_n)] = 𝔼^π_x[v'(X_0,A_0,…,X_n)]`
where `v'(xs,as) := ∫ v(xs,as,y_n) μ_n(dy_n|xs,as)` — the operational content of "`μ_n(·|X_0,
A_0,…,X_n)` is a conditional `ℙ^π_x`-distribution of `Y_n` given `(X_0,A_0,…,X_n)`", stated
without invoking a sub-σ-algebra conditional-expectation apparatus, matching how the book itself
uses exactly this identity (its Eq. (5.5)) to prove and to apply Theorem 5.2.1. The test
function is bounded, so that every expectation exists (the book's proviso for (5.5)); the
conditional-distribution statement is the case `v = 1_{B×C}`. -/
theorem theorem_5_2_1 {EX EY A : Type*} [MeasurableSpace EX] [MeasurableSpace EY]
    [MeasurableSpace A] [Nonempty A] (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M)
    (N : ℕ) (π : Policy EX A) (hπ : M.IsPolicy N π) (x0 : EX) (n : ℕ) (hn : n ≤ N)
    (v : (ℕ → EX) → (ℕ → A) → EY → ℝ)
    (hv_meas : Measurable fun p : (ℕ → EX) × (ℕ → A) × EY => v p.1 p.2.1 p.2.2)
    (hv_bdd : ∃ C : ℝ, ∀ xs as y, |v xs as y| ≤ C) :
    ∫ y0 : EY, M.Ex π n 0 (fun _ => x0) (fun _ => Classical.arbitrary A) y0
        (fun xs as y => v xs as y) ∂M.Q0 =
      ∫ y0 : EY, M.Ex π n 0 (fun _ => x0) (fun _ => Classical.arbitrary A) y0
        (fun xs as _ => ∫ yn, v xs as yn ∂(Fd.mu M n xs as).toMeasure) ∂M.Q0 := by sorry

end MDPFinance.POMDP
