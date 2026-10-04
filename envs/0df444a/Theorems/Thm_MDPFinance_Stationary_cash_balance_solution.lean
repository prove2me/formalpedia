-- Prove2me | Theorems.Thm_MDPFinance_Stationary_cash_balance_solution
-- name    : MDPFinance.Stationary.cash_balance_solution
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:46:48.950443+00:00
-- url     : https://prove2.me/theorems/e2ce0b2b-8bf4-4b94-9b32-9236088f8a44
-- title:
--   Theorem 2.6.2 — the cash balance problem (goal)
-- statement:
--   A firm's cash level $x \in \mathbb{R}$ evolves under i.i.d. shocks $Z_n$; each period the
--   firm may transfer to a new level $a$ at linear cost $c(a-x) := c_u(a-x)^+ + c_d(a-x)^-$
--   ($c_u,c_d>0$), pays a convex, coercive holding cost $L(a)$ ($L(0)=0$), and the level moves to
--   $a - Z_{n+1}$. Modeled as the stationary Markov Decision Model with $E=A=\mathbb{R}$,
--   $D(x)=\mathbb{R}$, $r(x,a) = -c(a-x)-L(a)$, $g \equiv 0$: there exist critical levels
--   $S_n^-\le S_n^+$ (depending on $n$) such that
--
--   $$
--   J_n(x) = \begin{cases}
--   (S_n^- - x)c_u + L(S_n^-) + \beta\,\mathbb{E}[J_{n-1}(S_n^- - Z)] & x < S_n^- \\
--   L(x) + \beta\,\mathbb{E}[J_{n-1}(x-Z)] & S_n^- \le x \le S_n^+ \\
--   (x-S_n^+)c_d + L(S_n^+) + \beta\,\mathbb{E}[J_{n-1}(S_n^+ - Z)] & x > S_n^+
--   \end{cases}
--   $$
--
--   with $J_0 \equiv 0$, and the optimal policy $f_n^*(x)$ transfers up to $S_n^-$ if $x<S_n^-$,
--   does nothing if $S_n^- \le x \le S_n^+$, and transfers down to $S_n^+$ if $x > S_n^+$.
--
--   **Formalization Note.** The critical levels $S_n^-, S_n^+$ are existentially quantified
--   functions of $n$ (not fixed constants) — a formalization dropping the $n$-dependence would be
--   a strictly different, false-in-general claim. $L$'s standing assumptions (convex, $L(0)=0$,
--   $\lim_{|x|\to\infty} L(x)/|x| = \infty$) are stated exactly as the book's own paragraph before
--   the theorem, not weakened. No trivializing specialization: $D(x) := \mathbb{R}$ for every $x$
--   is the book's own hypothesis, not a simplifying choice.
--
--   **Formalization Note (moderation).** The critical levels of part (b) are those of part (a)
--   (one existential quantifier covers both), and part (b) asserts what the book asserts: the
--   policy $(f_N^*,\dots,f_1^*)$ built from them by (2.6) attains $J_N$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 49, PDF 64, Theorem 2.6.2

import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model
import Definitions.Def_MDPFinance_Stationary_Policy
import Definitions.Def_MDPFinance_Stationary_Operators
import Definitions.Def_MDPFinance_Stationary_ValueFunction

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Stationary

/-- The cash-balance model's transfer-cost function `c(z) := c_u z^+ + c_d z^-`
(Bäuerle–Rieder, p. 47, PDF 62), for `c_u, c_d > 0`. -/
noncomputable def transferCost (cu cd : ℝ) (z : ℝ) : ℝ := cu * (max z 0) + cd * (max (-z) 0)

/-- Theorem 2.6.2 (Bäuerle–Rieder, p. 49, PDF 64) — the goal of this mission: the cash balance
problem. `M` is the stationary Markov Decision Model of §2.6.2 (p. 47, PDF 62): state space
`E := ℝ` (the cash level), action space `A := ℝ` (the post-transfer cash level), `D(x) := A`,
disturbances `(Z_n)` i.i.d. with finite expectation and law `μ_Z` (so `Q(\cdot\mid x,a)` is the
law of `a - Z`), reward `r(x,a) := -c(a-x) - L(a)` where `c(z) := c_u z^+ + c_d z^-`
(`c_u, c_d > 0`) is the transfer cost and `L : ℝ → ℝ_{\ge 0}` is a convex, coercive holding-cost
function with `L(0) = 0`; no terminal reward (`g ≡ 0`); discount `β ∈ (0,1]`. Then: a) there
exist critical levels `S_n^-, S_n^+` (depending on `n`) such that for `n = 1, …, N`, `J_n(x) =
(S_n^- - x) c_u + L(S_n^-) + β\,\mathbb{E}[J_{n-1}(S_n^- - Z)]` if `x < S_n^-`; `J_n(x) = L(x) +
β\,\mathbb{E}[J_{n-1}(x-Z)]` if `S_n^- \le x \le S_n^+`; `J_n(x) = (x-S_n^+)c_d + L(S_n^+) +
β\,\mathbb{E}[J_{n-1}(S_n^+ - Z)]` if `x > S_n^+`, with `J_0 ≡ 0`. b) The optimal cash-balance
policy is `(f_N^*, …, f_1^*)` where `f_n^*(x)` transfers to `S_n^-` if `x < S_n^-`, leaves `x`
unchanged if `S_n^- \le x \le S_n^+`, and transfers to `S_n^+` if `x > S_n^+`: the policy
`(f_N^*, …, f_1^*)` built from the critical levels of a) attains `J_N`. -/
theorem cash_balance_solution (M : StationaryMarkovDecisionModel ℝ ℝ) (cu cd : ℝ)
    (hcu : 0 < cu) (hcd : 0 < cd) (L : ℝ → ℝ) (hL_nonneg : ∀ x, 0 ≤ L x) (hL0 : L 0 = 0)
    (hL_convex : ConvexOn ℝ Set.univ L)
    (hL_coercive : Filter.Tendsto (fun x => L x / |x|) Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun x => L x / |x|) Filter.atBot Filter.atTop)
    (μZ : Measure ℝ) [IsProbabilityMeasure μZ] (hZ_integrable : Integrable id μZ)
    (hD : M.D = Set.univ) (hg : M.g = 0)
    (hQ : ∀ x a : ℝ, M.Q (x, a) = μZ.map (fun z => a - z))
    (hr : ∀ x a : ℝ, M.r (x, a) = -(transferCost cu cd (a - x)) - L a) (N : ℕ) :
    J M 0 = 0 ∧
    ∃ Sminus Splus : ℕ → ℝ,
      (∀ n, 1 ≤ n → n ≤ N → Sminus n ≤ Splus n ∧
        ∀ x : ℝ, J M n x =
          if x < Sminus n then
            ((Sminus n - x) * cu + L (Sminus n) : EReal) +
              (M.β : EReal) * erealIntegral μZ (fun z => J M (n - 1) (Sminus n - z))
          else if x ≤ Splus n then
            (L x : EReal) + (M.β : EReal) * erealIntegral μZ (fun z => J M (n - 1) (x - z))
          else
            ((x - Splus n) * cd + L (Splus n) : EReal) +
              (M.β : EReal) * erealIntegral μZ (fun z => J M (n - 1) (Splus n - z))) ∧
      Jpi M (fun k x =>
          if x < Sminus (N - k) then Sminus (N - k)
          else if x ≤ Splus (N - k) then x else Splus (N - k)) N = J M N := by sorry

end MDPFinance.Stationary
