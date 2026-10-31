-- Prove2me | Theorems.Thm_KallMayerSLP_Bonferroni_eq_3_15_boole_bonferroni
-- name    : KallMayerSLP.Bonferroni.eq_3_15_boole_bonferroni
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:16:22.233812+00:00
-- url     : https://prove2.me/theorems/1d60459e-8f81-4b17-ba1a-e8efcc728aeb
-- title:
--   Boole–Bonferroni bounds
-- statement:
--   Let $r\ge1$ and let $(\Omega,\mathcal F,\mathbb P)$ be a probability space.
--
--   1. For events $B_1,\dots,B_r$ with binomial moments $S_1,S_2$, the optimal value of the maximization counterpart of (3.14) is $V_{\max}=S_1-\frac2rS_2$, and $\mathbb P(B_1\cup\dots\cup B_r)\le V_{\max}$. If $S_1>0$, the optimal value of (3.14) is
--   $$
--   V_{\min}=\frac{2}{k^*+1}S_1-\frac{2}{k^*(k^*+1)}S_2,\qquad k^*=\left\lfloor\frac{2S_2}{S_1}\right\rfloor+1,
--   $$
--   and $V_{\min}\le\mathbb P(B_1\cup\dots\cup B_r)$.
--   2. For a random vector $\xi:\Omega\to\mathbb R^r$ with distribution function $F$ and $x\in\mathbb R^r$, with $B_i(x)=\{\xi_i>x_i\}$ and binomial moments $S_1(x),S_2(x)$,
--   $$
--   1-S_1(x)+\frac2rS_2(x)\le F(x),
--   $$
--   and, if $S_1(x)>0$,
--   $$
--   F(x)\le1-\frac{2}{k^*(x)+1}S_1(x)+\frac{2}{k^*(x)(k^*(x)+1)}S_2(x).
--   $$
--
--   The bounds are distribution-free: they use only the one- and two-dimensional marginals of $\xi$, through $S_1$ and $S_2$.
--
--   Differences from the source:
--   - encoding: events $B_1,\dots,B_r$ (or variables $v_1,\dots,v_r$) indexed by $1,\dots,r$ → indexed by `Fin r`, that is by $0,\dots,r-1$; reason: Lean convention; same instances
--   - encoding: the number $r$ of events $B_1,\dots,B_r$ (the dimension of $\xi$ with values in $\mathbb R^r$) is left implicit → hypothesis `1 ≤ r`; reason: the family $B_1,\dots,B_r$ starts at $B_1$, so the book has $r\ge1$; the hypothesis excludes only the empty family
--   - encoding: $k^*$ written without a condition on $S_1$ → the statements about $k^*$ assume $0<S_1$; reason: $k^*$ divides by $S_1$ and is undefined at $S_1=0$, where every $B_i$ is null; the condition excludes only that undefined case
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.15) with (3.9), p.288 (PDF 297)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
import Definitions.Def_KallMayerSLP_Bonferroni_exceedanceEvent
import Definitions.Def_KallMayerSLP_Bonferroni_jointCDF
import Definitions.Def_KallMayerSLP_Bonferroni_lpMin
import Definitions.Def_KallMayerSLP_Bonferroni_lpMax
import Definitions.Def_KallMayerSLP_Bonferroni_vMinClosedForm
import Definitions.Def_KallMayerSLP_Bonferroni_vMaxClosedForm

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- **Boole–Bonferroni bounds.** (a) For events `B₁, …, B_r` with binomial moments `S₁, S₂`, the
optimal values of (3.14) and of its maximization counterpart satisfy `V_max = S₁ - (2/r) S₂` and
`ℙ(B₁ ∪ ⋯ ∪ B_r) ≤ V_max`, and, if `S₁ > 0`, `V_min = 2/(k*+1) S₁ - 2/(k*(k*+1)) S₂` and
`V_min ≤ ℙ(B₁ ∪ ⋯ ∪ B_r)`, with `k* = ⌊2 S₂ / S₁⌋ + 1`.
(b) For a random vector `ξ` and `x ∈ ℝ^r`, with `B_i(x) = {ξ_i > x_i}`:
`1 - S₁(x) + (2/r) S₂(x) ≤ F(x)`, and, if `S₁(x) > 0`,
`F(x) ≤ 1 - 2/(k*(x)+1) S₁(x) + 2/(k*(x)(k*(x)+1)) S₂(x)`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.15) with (3.9), p.288 (PDF 297).

**Formalization Note.** The book's `k*` needs `S₁ > 0`. The bounds are distribution-free: nothing
is assumed about `ξ` beyond measurability. `vMaxClosedForm` is not capped at `1`. -/
theorem eq_3_15_boole_bonferroni {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) :
    (∀ B : Fin r → Set Ω, (∀ i, MeasurableSet (B i)) →
      lpMax r (binomialMoment μ B 1) (binomialMoment μ B 2) =
        vMaxClosedForm r (binomialMoment μ B 1) (binomialMoment μ B 2) ∧
      μ.real (⋃ i, B i) ≤ vMaxClosedForm r (binomialMoment μ B 1) (binomialMoment μ B 2) ∧
      (0 < binomialMoment μ B 1 →
        lpMin r (binomialMoment μ B 1) (binomialMoment μ B 2) =
          vMinClosedForm (binomialMoment μ B 1) (binomialMoment μ B 2) ∧
        vMinClosedForm (binomialMoment μ B 1) (binomialMoment μ B 2) ≤ μ.real (⋃ i, B i))) ∧
    (∀ ξ : Ω → Fin r → ℝ, Measurable ξ → ∀ x : Fin r → ℝ,
      1 - binomialMoment μ (exceedanceEvent ξ x) 1 +
          2 / (r : ℝ) * binomialMoment μ (exceedanceEvent ξ x) 2 ≤ jointCDF μ ξ x ∧
      (0 < binomialMoment μ (exceedanceEvent ξ x) 1 →
        jointCDF μ ξ x ≤
          1 - vMinClosedForm (binomialMoment μ (exceedanceEvent ξ x) 1)
                (binomialMoment μ (exceedanceEvent ξ x) 2))) := by sorry

end KallMayerSLP.Bonferroni
