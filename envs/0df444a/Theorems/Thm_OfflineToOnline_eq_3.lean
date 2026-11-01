-- Prove2me | Theorems.Thm_OfflineToOnline_eq_3
-- name    : OfflineToOnline.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:04.487184+00:00
-- url     : https://prove2.me/theorems/691c0da4-1ef0-4790-95a2-8ea132645e44
-- title:
--   Display (3) — Online-IG's payoff sums satisfy $[\sum_t \textsc{Payoff}(\theta_t^{(i)},z_t^{(i-1)},f_t)]_j\ge -Tg(T)$
-- statement:
--   Let an instance of Algorithm 1 be Blackwell reducible via $(\mathcal Y,\boldsymbol p,\mathrm{AdvB})$, let $T\ge1$ and $g\ge0$, and let $\mathrm{AlgB}$ be a payoff-based Blackwell algorithm with actions in $\Theta$ that approaches the nonnegative orthant at horizon $T$ with $\ell_\infty$ rate $g$. Let $f_1,\dots,f_T\in\mathcal F$ and let $\theta_t^{(i)}$, $z_t^{(i)}$ be the parameters and points of Online-IG with $\mathrm{AlgB}$. Then on every realization of the random seeds, for every subproblem $i\in[N]$ and every coordinate $j\in[d_{\mathrm{payoff}}]$,
--
--   $$
--   \Big[\sum_{t=1}^T\textsc{Payoff}\big(\theta_t^{(i)},z_t^{(i-1)},f_t\big)\Big]_j\ \ge\ -T\,g .
--   $$
--
--   This is the slack condition of Definition 6 with $h(T)=Tg$; together with robustness it yields the regret bound of Theorem 2.
--
--   Differences from the source:
--   - reading: θ_t^(i) chosen by N parallel instances AlgB^(i) of AlgB → every subproblem runs the same payoff-based strategy A on its own history; reason: "Initialize N parallel instances {AlgB(i)} of the online algorithm AlgB" (Algorithm 2)
--   - encoding: g(T) rate of AlgB from Theorem 1; rounds 1..T, subproblems 1..N → any g ≥ 0 with Approaches at horizon T ≥ 1; 0-indexed rounds and subproblems; the bound for every seed realization; reason: the page's argument is pathwise and uses only the approachability guarantee at T
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, display (3), p.22 (with the p.21 displays before it)

import Mathlib
import Definitions.Def_OfflineToOnline_IsBiaffineOn
import Definitions.Def_OfflineToOnline_IsResponseSatisfiable
import Definitions.Def_OfflineToOnline_IGInstance
import Definitions.Def_OfflineToOnline_runPoints
import Definitions.Def_OfflineToOnline_payoffPlay
import Definitions.Def_OfflineToOnline_Approaches
import Definitions.Def_OfflineToOnline_orthant
import Definitions.Def_OfflineToOnline_IsBlackwellReducible
import Definitions.Def_OfflineToOnline_onlineIG

universe u v

namespace OfflineToOnline

/-- **Display (3)**: if the instance is Blackwell reducible via `(Y, p, AdvB)` and the Blackwell
algorithm `A` (actions in `Θ`) approaches the orthant at horizon `T` with ℓ∞ rate `g ≥ 0`, then the
parameters of Online-IG satisfy, on every seed realization, for every subproblem `i` and every
coordinate `j`,
`[∑_{t=1}^T Payoff(θ_t^(i), z_t^(i−1), f_t)]_j ≥ −T g(T)`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, (3), p.22 (with the p.21 display before it).

Formalization Note: rounds and subproblems are `0`-indexed: the page's `θ_t^(i)` is
`onlineIG I A f t ⟨i − 1, _⟩ ω` and `z_t^(i−1)` is `runPoints I (onlineIG I A f) t (i − 1) ω`. The
bound holds pathwise, for every seed realization `ω`. -/
theorem eq_3 {D : Type u} {Ω : Type v} [MeasurableSpace D] [MeasurableSpace Ω] {m k d : ℕ}
    (I : IGInstance D Ω m d) (Y : Set (Fin k → ℝ)) (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ))
    (AdvB : D → (D → ℝ) → (Fin k → ℝ)) (hred : IsBlackwellReducible I Y p AdvB)
    (T : ℕ) (hT : 1 ≤ T) (g : ℝ) (hg : 0 ≤ g) (A : PayoffStrategy m d)
    (hA : Approaches p I.Θ Y (orthant d) A T g) (f : Fin T → D → ℝ) (hf : ∀ t, f t ∈ I.F)
    (ω : Fin T → Fin I.N → Ω) (i : Fin I.N) (j : Fin d) :
    -(T * g) ≤
      (∑ t, I.payoff (onlineIG I A f t i ω) (runPoints I (onlineIG I A f) t i ω) (f t)) j := by sorry

end OfflineToOnline
