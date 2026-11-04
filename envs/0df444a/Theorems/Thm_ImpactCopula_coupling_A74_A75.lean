-- Prove2me | Theorems.Thm_ImpactCopula_coupling_A74_A75
-- name    : ImpactCopula.coupling_A74_A75
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:57:32.433607+00:00
-- url     : https://prove2.me/theorems/fa5e3ca5-5aae-4681-b1b7-53f3be6e49a9
-- title:
--   Step four, (A.74)–(A.75) — $(X_i,\theta_i) \overset{d}{=} (F_X^{-1}(U_i), \tilde g(F_X(F_X^{-1}(U_i)), V_i))$
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^2$ (the law of $(X_i, \theta_i)$) and $C$ a copula of $\mu$ that is linearly interpolating on $\overline{\mathcal R}_X^c \times \overline{\mathcal R}_\theta$ with respect to $u$. Let $U_i, V_i$ be independent and uniform on $(0,1)$. Then
--
--   $$
--   (X_i, \theta_i) \overset{d}{=} \Big(F_X^{-1}(U_i),\ \tilde g\big(F_X(F_X^{-1}(U_i)), V_i\big)\Big),
--   $$
--
--   where $\tilde g$ is the modified mixture function (A.71). That is, $P(F_X^{-1}(U_i) \le x, \tilde g(F_X(F_X^{-1}(U_i)), V_i) \le y) = C(F_X(x), F_\theta(y)) = P(X_i \le x, \theta_i \le y)$ for all $x, y$.
--
--   This coupling builds each observation from two uniforms, so that the rank of $X_i$ is driven by $U_i$ alone.
--
--   Differences from the source:
--   - reading: "For any $x, y \in [0,1]$" in (A.74) → all $x, y \in \mathbb R$ (equality in law of $\mathbb R^2$-valued vectors); reason: (A.74)–(A.75) use $F_X(x)$, $F_\theta(y)$ for real $x, y$ and conclude equality in distribution, which needs every $x, y \in \mathbb R$.
--   - encoding: $\overset{d}{=}$, $(U_i, V_i)$ → `IdentDistrib` (equal laws, both maps a.e.-measurable) of the identity under $\mu$ and the map $(u, w) \mapsto (\dots)$ under Lebesgue measure on $[0,1]^2$; reason: Lean convention; same statement.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix C.3, proof of Theorem 2, step four, eqs. (A.74)–(A.75), pp.80–81 (PDF pp.83–84)

import Mathlib
import Definitions.Def_ImpactCopula_IsCopulaOf
import Definitions.Def_ImpactCopula_IsLinearlyInterpolating
import Definitions.Def_ImpactCopula_mixtureTilde

open MeasureTheory ProbabilityTheory

namespace ImpactCopula

/-- **Step four of the proof of Theorem 2**, (A.74)–(A.75), Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), pp.80–81 (PDF pp.83–84): for a
linearly interpolating copula `C` of `F`, `(X_i, θ_i) =d (F_X⁻¹(U_i), g̃(F_X(F_X⁻¹(U_i)), V_i))`,
where `U_i, V_i` are independent `Uniform(0, 1)`.

**Formalization Note.** Equality in distribution is `IdentDistrib`: the identity under the law
`μ` of `(X_i, θ_i)` and the map `(u, w) ↦ (F_X⁻¹(u), g̃(F_X(F_X⁻¹(u)), w))` under the uniform law
on `[0, 1]²` (product of two copies of `volume.restrict (Icc 0 1)`) have the same law, and both
are a.e.-measurable. The paper's "for any x, y ∈ [0, 1]" in (A.74) is read as `x, y ∈ ℝ`, the
range needed for equality in distribution of `ℝ²`-valued vectors. -/
theorem coupling_A74_A75 (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (C : ℝ → ℝ → ℝ)
    (hC : IsCopulaOf C μ) (hLI : IsLinearlyInterpolating C μ) :
    IdentDistrib (id : ℝ × ℝ → ℝ × ℝ)
      (fun q : ℝ × ℝ =>
        (RiskFunctionals.StochDominance.quantileFunction (μ.map Prod.fst) q.1,
          mixtureTilde C μ
            (cdfX μ (RiskFunctionals.StochDominance.quantileFunction (μ.map Prod.fst) q.1)) q.2))
      μ ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by sorry

end ImpactCopula
