-- Prove2me | Theorems.Thm_ImpactCopula_eq_A76
-- name    : ImpactCopula.eq_A76
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:57:40.875523+00:00
-- url     : https://prove2.me/theorems/056ebfec-326d-4ea8-84c7-01402526d46f
-- title:
--   Eq. (A.76) — $\theta_{[X]} \overset{d}{=} (\tilde g(F_X(F_X^{-1}(U_{i:N})), V_i))_{i}$
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^2$ and $C$ a copula of $\mu$ that is linearly interpolating on $\overline{\mathcal R}_X^c \times \overline{\mathcal R}_\theta$ with respect to $u$. For $N \ge 1$, let $(X_1,\theta_1), \dots, (X_N,\theta_N)$ be i.i.d. with law $\mu$ (Assumption (A1)), and $\theta_{[1:N]}, \dots, \theta_{[N:N]}$ the induced order statistics of the $\theta_i$ ranked by the $X_i$. Let $U_1, \dots, U_N, V_1, \dots, V_N$ be independent uniform on $(0,1)$ with order statistics $U_{1:N} \le \dots \le U_{N:N}$. Then
--
--   $$
--   \big(\theta_{[1:N]}, \dots, \theta_{[N:N]}\big) \overset{d}{=} \Big(\tilde g\big(F_X(F_X^{-1}(U_{1:N})), V_1\big), \dots, \tilde g\big(F_X(F_X^{-1}(U_{N:N})), V_N\big)\Big). \tag{A.76}
--   $$
--
--   Together with (A.73) this gives the "if" half of Theorem 2.
--
--   Differences from the source:
--   - reading: ranking of tied $X_i$ (unspecified; ties have positive probability when $F_X$ has atoms) → ties broken by index (published `inducedOrderStat`); reason: the law of $\theta_{[X]}$ is the same under every tie rule that is a function of $X$ (given $X$, the $\theta_i$ are conditionally independent with laws depending on $X_i$ only).
--   - encoding: the i.i.d. sample, ranks, $\overset{d}{=}$ → `Measure.pi (fun _ => μ)` on `Fin N → ℝ × ℝ`, 0-based ranks, `IdentDistrib` against `unifPair N`; reason: Lean convention; same statement.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix C.3, proof of Theorem 2, step five, eq. (A.76), p.81 (PDF p.84)

import Mathlib
import Definitions.Def_ImpactCopula_IsCopulaOf
import Definitions.Def_ImpactCopula_IsLinearlyInterpolating
import Definitions.Def_ImpactCopula_mixtureTilde
import Definitions.Def_ImpactCopula_unifPair
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat

open MeasureTheory ProbabilityTheory

namespace ImpactCopula

/-- **(A.76)**, proof of Theorem 2, step five, Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.81 (PDF p.84): for a linearly interpolating
copula `C` of `F` and every `N ≥ 1`,
`(θ_[1:N], …, θ_[N:N]) =d (g̃(F_X(F_X⁻¹(U_{1:N})), V_1), …, g̃(F_X(F_X⁻¹(U_{N:N})), V_N))`.

**Formalization Note.** The sample `(X_i, θ_i)_{i ≤ N}` of Assumption (A1) has law
`Measure.pi (fun _ => μ)` on `Fin N → ℝ × ℝ`; `θ_[X]` is the published `inducedOrderStat` of
the `θ_i` ranked by the `X_i` (0-based ranks, ties broken by index, which changes no law);
`(U, V)` has law `unifPair N` and `U_{i:N}` is the published `orderStat`. `=d` is
`IdentDistrib`. -/
theorem eq_A76 (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (C : ℝ → ℝ → ℝ)
    (hC : IsCopulaOf C μ) (hLI : IsLinearlyInterpolating C μ) (N : ℕ) (hN : 1 ≤ N) :
    IdentDistrib
      (fun s : Fin N → ℝ × ℝ =>
        ImpactInvesting.Portfolio.inducedOrderStat (fun i => (s i).1) (fun i => (s i).2))
      (fun p : (Fin N → ℝ) × (Fin N → ℝ) => fun i =>
        mixtureTilde C μ
          (cdfX μ (RiskFunctionals.StochDominance.quantileFunction (μ.map Prod.fst)
            (ImpactInvesting.Portfolio.orderStat p.1 i)))
          (p.2 i))
      (Measure.pi fun _ : Fin N => μ) (unifPair N) := by sorry

end ImpactCopula
