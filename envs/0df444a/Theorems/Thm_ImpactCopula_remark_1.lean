-- Prove2me | Theorems.Thm_ImpactCopula_remark_1
-- name    : ImpactCopula.remark_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:55:00.965411+00:00
-- url     : https://prove2.me/theorems/304ec4a5-e876-4a8e-a022-033c42446bc3
-- title:
--   Remark 1 — $D_1C$ is a regular conditional distribution function of $C$ given $u$
-- statement:
--   Let $C$ be a copula and $D_1C$ its modified partial Dini derivative (A.30). Then:
--
--   1. for every $u \in [0,1]$, $v \mapsto D_1C(u,v)$ is a distribution function on $\mathbb R$;
--   2. for every $v \in [0,1]$, $u \mapsto D_1C(u,v)$ is Lebesgue measurable on $[0,1]$ and
--
--   $$
--   \int_0^a D_1C(u,v)\,du = C(a,v) \qquad \text{for every } a \in [0,1].
--   $$
--
--   This is Theorem 2.1 of Fang, Madsen and Liu (2020), which the paper cites without proof. It allows one to write $\mathbb P(V \le v \mid U = u) = D_1C(u,v)$ for any copula, differentiable or not.
--
--   Differences from the source:
--   - encoding: "distribution function", "Lebesgue measurable", $\int_0^a$ → `IsDistributionFunction` (monotone, right-continuous, limits $0$ and $1$), `AEMeasurable` for Lebesgue measure on $[0,1]$, interval integral; reason: Lean convention; same instances.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix A.3.1, Remark 1, p.42 (PDF p.45), citing Fang–Madsen–Liu (2020), Theorem 2.1

import Mathlib
import Definitions.Def_actuarial_coIsCopula
import Definitions.Def_ImpactCopula_mpdd
import Definitions.Def_ImpactCopula_IsDistributionFunction

open MeasureTheory

namespace ImpactCopula

/-- **Remark 1** (Fang et al. 2020, Theorem 2.1), Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.42 (PDF p.45): `D₁C` defined by (A.30)
is a regular conditional distribution function of `C` given `u`: (i) for any `u ∈ [0, 1]`,
`v ↦ D₁C(u, v)` is a distribution function; (ii) for any `v ∈ [0, 1]`, `u ↦ D₁C(u, v)` is
Lebesgue measurable and `∫₀^a D₁C(u, v) du = C(a, v)` for any `a ∈ [0, 1]`.

**Formalization Note.** "Distribution function" is `IsDistributionFunction` (monotone,
right-continuous, limits `0` and `1`). "Lebesgue measurable" on `[0, 1]` is `AEMeasurable` with
respect to Lebesgue measure restricted to `[0, 1]`. The integral is the interval integral
`∫ u in 0..a`. -/
theorem remark_1 (C : ℝ → ℝ → ℝ) (hC : ActuarialValuation.coIsCopula C) :
    (∀ u ∈ Set.Icc (0 : ℝ) 1, IsDistributionFunction (mpdd C u)) ∧
      ∀ v ∈ Set.Icc (0 : ℝ) 1,
        AEMeasurable (fun u => mpdd C u v) (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
          ∀ a ∈ Set.Icc (0 : ℝ) 1, ∫ u in (0 : ℝ)..a, mpdd C u v = C a v := by sorry

end ImpactCopula
