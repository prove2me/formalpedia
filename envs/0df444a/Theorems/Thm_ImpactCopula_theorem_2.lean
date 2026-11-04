-- Prove2me | Theorems.Thm_ImpactCopula_theorem_2
-- name    : ImpactCopula.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:57:19.515212+00:00
-- url     : https://prove2.me/theorems/d6902be0-6802-48d1-a259-aea72920a66e
-- title:
--   Theorem 2 (Representation Theorem for General $F$) — $\theta_{[X]} \overset{d}{=} (g(U_{i:N},V_i))_i$ for every $N$ iff $C$ is linearly interpolating
-- statement:
--   Let $(X_1,\theta_1), \dots, (X_N,\theta_N)$ be i.i.d. with an arbitrary joint law $F$ on $\mathbb R^2$ (Assumption (A1)), with marginal distribution functions $F_X$, $F_\theta$, and let $C$ be a copula of $F$, i.e. $F(x,y) = C(F_X(x), F_\theta(y))$ for all $x, y$. Let $\theta_{[1:N]}, \dots, \theta_{[N:N]}$ be the induced order statistics of the $\theta_i$ ranked by the $X_i$. Let $U_1,\dots,U_N,V_1,\dots,V_N$ be mutually independent and uniform on $(0,1)$, with order statistics $U_{1:N} \le \dots \le U_{N:N}$, and define the mixture function
--
--   $$
--   g(u, w) = F_\theta^{-1}\big(g_u(w)\big), \tag{15}
--   $$
--
--   where $g_u$ is the inverse function of $v \mapsto D_1C(u,v)$, the modified partial Dini derivative (A.30), and $F_\theta^{-1}(p) = \inf\{x : F_\theta(x) \ge p\}$. Then
--
--   $$
--   \big(\theta_{[1:N]}, \theta_{[2:N]}, \dots, \theta_{[N:N]}\big) \overset{d}{=} \big(g(U_{1:N}, V_1), g(U_{2:N}, V_2), \dots, g(U_{N:N}, V_N)\big) \tag{14}
--   $$
--
--   holds **for every $N \ge 1$** if and only if $C$ is linearly interpolating on $\overline{\mathcal R}_X^c \times \overline{\mathcal R}_\theta$ with respect to $u$ (Definition 1).
--
--   No continuity, density or differentiability is assumed: $X_i$ and $\theta_i$ may have atoms and $C$ may be any copula of $F$. When $F_X$ is continuous the condition is empty, which recovers Theorem 1. For a single $N$ the representation can hold without the condition (for $N = 1$ it holds for every copula); the equivalence is with (14) for all $N$ simultaneously.
--
--   Differences from the source:
--   - reading: ranking of tied $X_i$ (unspecified; ties have positive probability when $F_X$ has atoms) → ties broken by index (published `inducedOrderStat`); reason: the law of $\theta_{[X]}$ is the same under every tie rule that is a function of $X$.
--   - encoding: Assumption (A1), "$\overset{d}{=}$", ranks $1,\dots,N$ → law `Measure.pi (fun _ => μ)` of the sample, `IdentDistrib` (equal laws, both vectors a.e.-measurable) against `unifPair N`, 0-based ranks `Fin N`; reason: Lean convention; same statement.
--   - encoding: generalized inverses with values $\pm\infty$ → real-valued `sInf`s (`condInv`, published `quantileFunction`); reason: they differ only on a Lebesgue-null set of $(u, w)$ (by Remark 1 (ii)), which changes no law.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Theorem 2, eqs. (14)–(15), p.12 (PDF p.15)

import Mathlib
import Definitions.Def_ImpactCopula_IsCopulaOf
import Definitions.Def_ImpactCopula_IsLinearlyInterpolating
import Definitions.Def_ImpactCopula_mixture
import Definitions.Def_ImpactCopula_unifPair
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat

open MeasureTheory ProbabilityTheory

namespace ImpactCopula

/-- **Theorem 2 (Representation Theorem for General F)**, Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.12 (PDF p.15): "Under
Assumption (A1), we have (θ_[1:N], θ_[2:N], …, θ_[N:N]) =d (g(U_{1:N}, V_1), g(U_{2:N}, V_2), …,
g(U_{N:N}, V_N)) (14) for any N ≥ 1 if and only if the copula C(u, v) is linearly interpolating on
R̄_X^c × R̄_θ with respect to u. Here, the function g is defined as g(u, w) ≡ F_θ⁻¹ ∘ g_u(w) (15),
where g_u(w) is the inverse function of v ↦ D₁C(u, v), and D₁C(u, v) is defined by (A.30)."

**Formalization Note.** The bivariate law `F` is an arbitrary probability measure `μ` on `ℝ²`
(no continuity or density), `C` is any copula of `μ` ((10), `IsCopulaOf`), and the sample of
Assumption (A1) has law `Measure.pi (fun _ => μ)` on `Fin N → ℝ × ℝ`. `θ_[X]` is the published
`inducedOrderStat` (0-based ranks; ties among the `X_i`, which occur with positive probability
when `F_X` has atoms, are broken by index, which changes no law). `(U, V)` has law `unifPair N`,
`U_{i:N}` is the published `orderStat`. `=d` is `IdentDistrib`, which also asserts that both
vectors are a.e.-measurable. `g` is `mixture`: real-valued generalized inverses, whose junk values
(the paper's `±∞`) occur only on a Lebesgue-null set of `(u, w)` and change no law. The
quantifier "for any N ≥ 1" sits inside the left side of the equivalence, as printed. -/
theorem theorem_2 (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (C : ℝ → ℝ → ℝ)
    (hC : IsCopulaOf C μ) :
    (∀ N : ℕ, 1 ≤ N →
      IdentDistrib
        (fun s : Fin N → ℝ × ℝ =>
          ImpactInvesting.Portfolio.inducedOrderStat (fun i => (s i).1) (fun i => (s i).2))
        (fun p : (Fin N → ℝ) × (Fin N → ℝ) => fun i =>
          mixture C μ (ImpactInvesting.Portfolio.orderStat p.1 i) (p.2 i))
        (Measure.pi fun _ : Fin N => μ) (unifPair N)) ↔
      IsLinearlyInterpolating C μ := by sorry

end ImpactCopula
