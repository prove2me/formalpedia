-- Prove2me | Theorems.Thm_KAdaptability_EpsApprox_proposition_2
-- name    : KAdaptability.EpsApprox.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:03:14.6866+00:00
-- url     : https://prove2.me/theorems/df099d34-e194-41de-9c4d-3ba4caf0fe47
-- title:
--   Proposition 2 — dom(6_ε) = dom(6) for small ε, and the objectives of (6_ε) converge uniformly to that of (6)
-- statement:
--   Let an instance of the two-stage robust binary program with constraint uncertainty be given, with $\mathcal X\subseteq\{0,1\}^N$, $\mathcal Y\subseteq\{0,1\}^M$ and $\Xi=\{\xi:A\xi\le b\}$ nonempty and bounded, and let $K\in\mathbb N$ be the number of policies. Denote by $\varphi$ and $\varphi_\varepsilon$ the objective functions of problems (6) and $(6_\varepsilon)$, and by $\mathrm{dom}(6)$ and $\mathrm{dom}(6_\varepsilon)$ their effective domains: the decisions $(x,\{y^k\}_{k\in\mathcal K})\in\mathcal X\times\mathcal Y^K$ at which the objective value is finite (not $+\infty$). Then:
--
--   1. $\mathrm{dom}(6_\varepsilon)=\mathrm{dom}(6)$ for all sufficiently small $\varepsilon>0$: there is $\varepsilon_0>0$ with
--   $$\mathrm{dom}(6_\varepsilon)=\mathrm{dom}(6)\qquad\text{for all }\varepsilon\in(0,\varepsilon_0];$$
--   2. over the effective domain, $\varphi_\varepsilon$ converges uniformly to $\varphi$ as $\varepsilon\downarrow0$: for every $\kappa>0$ there is $\varepsilon_0>0$ such that for all $\varepsilon\in(0,\varepsilon_0]$ and all $(x,\{y^k\})\in\mathrm{dom}(6)$ the values $\varphi(x,\{y^k\})$ and $\varphi_\varepsilon(x,\{y^k\})$ are real numbers with
--   $$\big|\varphi_\varepsilon(x,\{y^k\})-\varphi(x,\{y^k\})\big|\le\kappa .$$
--
--   Since (6) is equivalent to the K-adaptability problem $\mathcal P_K$ (Proposition 1), this justifies solving the problems $(6_\varepsilon)$, whose uncertainty sets are closed, in place of $\mathcal P_K$.
--
--   **Formalization Note** Objective values are extended reals; "finite (i.e., do not evaluate to $+\infty$)" is read as $<+\infty$, as the paper says. Part (ii) is stated with a single threshold $\varepsilon_0$ that works for every decision of $\mathrm{dom}(6)$ at once, which is what "uniformly" means; since by (i) the two domains coincide for small $\varepsilon$, "over their effective domains" is the domain of (6). The remark after the proposition (convergence of the optimal values) is not part of the statement.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), pp. 18–19, Proposition 2; proof pp. ec7–ec8 (PDF pp. 41–42)

import Mathlib
import Definitions.Def_KAdaptability_EpsApprox_Approx

namespace KAdaptability.EpsApprox

open Problem

/-- **Proposition 2** (pp. 18–19). With `𝒳 ⊆ {0,1}^N`, `𝒴 ⊆ {0,1}^M` and `Ξ` a nonempty bounded
polyhedron (all part of `Problem`), and any number `K` of policies:
(i) `dom(6_ε) = dom(6)` for all sufficiently small `ε > 0`; and
(ii) over the effective domain, the objective functions of (6_ε) converge uniformly to the
objective function of (6) as `ε ↓ 0`: for every `κ > 0` there is `ε₀ > 0` such that for every
`ε ∈ (0, ε₀]` and every decision in `dom(6)` both objective values are real numbers within `κ`
of each other. -/
theorem proposition_2 {N M L nQ R : ℕ} (P : Problem N M L nQ R) (K : ℕ) :
    (∃ ε₀ > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε₀, P.dom6Eps K ε = P.dom6 K) ∧
    (∀ κ > 0, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε₀, ∀ d ∈ P.dom6 K,
      ∃ φ φε : ℝ, P.obj6 d.1 d.2 = (φ : EReal) ∧ P.obj6Eps ε d.1 d.2 = (φε : EReal) ∧
        |φε - φ| ≤ κ) := by sorry

end KAdaptability.EpsApprox
