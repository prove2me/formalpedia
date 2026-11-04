-- Prove2me | Theorems.Thm_ImpactCopula_eq_A78
-- name    : ImpactCopula.eq_A78
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:57:32.824818+00:00
-- url     : https://prove2.me/theorems/baf69e10-8e2b-4224-85f5-e8e6566420ba
-- title:
--   Eq. (A.78) — induced order statistics of the coupled sample
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^2$ and $C$ a copula of $\mu$ that is linearly interpolating on $\overline{\mathcal R}_X^c \times \overline{\mathcal R}_\theta$ with respect to $u$. Fix $N \ge 1$, let $U_1, \dots, U_N, V_1, \dots, V_N$ be independent uniform on $(0,1)$, and put
--
--   $$
--   H_i = F_X^{-1}(U_i), \qquad W_i = \tilde g\big(F_X(H_i), V_i\big).
--   $$
--
--   Let $H_{1:N} \le \dots \le H_{N:N}$ be the order statistics of the $H_i$ and $W_{[1:N]}, \dots, W_{[N:N]}$ the induced order statistics of the $W_i$ ranked by the $H_i$. Then
--
--   $$
--   \big(W_{[1:N]}, \dots, W_{[N:N]}\big) \overset{d}{=} \Big(\tilde g\big(F_X(H_{1:N}), V_1\big), \dots, \tilde g\big(F_X(H_{N:N}), V_N\big)\Big). \tag{A.78}
--   $$
--
--   The noise attached to the $k$-th ranked observation can be replaced by the $k$-th noise variable, because the noise is independent of the ranking.
--
--   Differences from the source:
--   - reading: ranking of tied $H_i$ (unspecified; ties have positive probability when $F_X$ has atoms) → ties broken by index (`Tuple.sort`, published `inducedOrderStat`/`orderStat`); reason: the law of the left side is the same for every tie rule that is a function of $H$, since $(V_{\sigma(k)})_k$ has the law of $(V_k)_k$ independently of $H$.
--   - encoding: ranks $1, \dots, N$, $\overset{d}{=}$, the law of $(U, V)$ → 0-based ranks `Fin N`, `IdentDistrib`, `unifPair N`; reason: Lean convention; same statement.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix C.3, proof of Theorem 2, step five, eq. (A.78), pp.81–82 (PDF pp.84–85)

import Mathlib
import Definitions.Def_ImpactCopula_IsCopulaOf
import Definitions.Def_ImpactCopula_IsLinearlyInterpolating
import Definitions.Def_ImpactCopula_mixtureTilde
import Definitions.Def_ImpactCopula_unifPair
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat

open MeasureTheory ProbabilityTheory

namespace ImpactCopula

/-- **(A.78)**, proof of Theorem 2, step five, Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), pp.81–82 (PDF pp.84–85): with
`H_i = F_X⁻¹(U_i)` and `W_i = g̃(F_X(H_i), V_i)`, the induced order statistics
`(W_[1:N], …, W_[N:N])` of the `W_i` ranked by the `H_i` satisfy
`(W_[1:N], …, W_[N:N]) =d (g̃(F_X(H_{1:N}), V_1), …, g̃(F_X(H_{N:N}), V_N))`.

**Formalization Note.** `(U, V)` has law `unifPair N`. Ranks are 0-based (`i : Fin N` is the
paper's `i + 1`). `H_{i:N}` is the published `orderStat` and `W_[i:N]` the published
`inducedOrderStat` (ties among the `H_i`, which have positive probability when `F_X` has atoms,
are broken by index through `Tuple.sort`; this changes no law). `=d` is `IdentDistrib`. The
standing hypotheses of the "if" part (a linearly interpolating copula `C` of `F`) are kept. -/
theorem eq_A78 (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (C : ℝ → ℝ → ℝ)
    (hC : IsCopulaOf C μ) (hLI : IsLinearlyInterpolating C μ) (N : ℕ) (hN : 1 ≤ N) :
    IdentDistrib
      (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
        ImpactInvesting.Portfolio.inducedOrderStat
          (fun j => RiskFunctionals.StochDominance.quantileFunction (μ.map Prod.fst) (p.1 j))
          (fun j => mixtureTilde C μ
            (cdfX μ (RiskFunctionals.StochDominance.quantileFunction (μ.map Prod.fst) (p.1 j)))
            (p.2 j)))
      (fun p : (Fin N → ℝ) × (Fin N → ℝ) => fun i =>
        mixtureTilde C μ
          (cdfX μ (ImpactInvesting.Portfolio.orderStat
            (fun j => RiskFunctionals.StochDominance.quantileFunction (μ.map Prod.fst) (p.1 j)) i))
          (p.2 i))
      (unifPair N) (unifPair N) := by sorry

end ImpactCopula
