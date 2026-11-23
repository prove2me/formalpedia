-- Prove2me | Theorems.Thm_LargeBSP_Homog_Supplement_theorem_4
-- name    : LargeBSP.Homog.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T16:56:08.19436+00:00
-- url     : https://prove2.me/theorems/e8573e5e-28a9-4df1-b7c5-72a5069b7f6d
-- title:
--   Theorem 4, p. 16 (corrected: c̄(t) in argmax, c = 0 and t = 0, positive gain) — cost-dependent valuations
-- statement:
--   Let the costs $c_n\ge0$ be bounded with empirical distribution functions converging to $F_C$ (Assumption 3). Let $X_n=c_nZ_n$, where the $Z_n\ge0$ are i.i.d. with continuous distribution function $F_Z$ and finite mean (Assumption 4). Let $F_X$ be the distribution function of $CZ$ for independent $C\sim F_C$ and $Z\sim F_Z$. Write $\bar V_N,\bar c_N$ for the normalized value and cost curves. Then:
--
--   1. $F_X(x)=\int F_Z(x/c)\,dF_C(c)$ for every $x$, the integrand at $c=0$ being $\mathbf 1\{x\ge0\}$;
--   2. for every $t\in[0,1]$, in probability, $\bar V_N(t)\Rightarrow\bar V(t)=\int_0^tF_X^{-1}(1-s)\,ds$ and
--   $$\bar c_N(t)\Rightarrow\bar c(t)=\int c\,\bigl(1-F_Z(F_X^{-1}(1-t)/c)\bigr)\,dF_C(c),$$
--   with $\bar c(0)=0$;
--   3. $\bar V-\bar c$ has a maximizer on $[0,1]$;
--   4. for every maximizer $t^\star$ whose gain $J(t^\star)=\int\!\int_{F_X^{-1}(1-t^\star)/c}^\infty c(z-1)\,dF_Z(z)\,dF_C(c)$ is positive,
--   $$\lim_{N\to\infty}\frac{\mathbb E[\pi(p_N^\star)]}{N\,J(t^\star)}=1.$$
--
--   This gives the first-order value of bundle-size pricing when expensive items are also valued more.
--
--   **Formalization Note** The valuations $X_n$ are independent but not identically distributed. Zero costs are allowed. The optimal profit is a supremum over menus.
--
--   Differences from the source:
--
--   - encoding: items and order statistics are indexed from 1, ties between equally good sizes are unspecified, and ⇒ denotes a limit → items are indexed from 0, the customer takes the smallest of equally good sizes, and ⇒ is convergence in probability; reason: these are the conventions of the mission's model, and every limit here is a constant
--   - correction: t⋆ maximizes V̄(t) − c(t) → t⋆ maximizes V̄(t) − c̄(t), with existence asserted and (18) stated for every maximizer; reason: c(t) is not defined, and (A12) on p. A6 identifies the limiting profit as V̄(t) − c̄(t)
--   - correction: F_Z(x/c) and F_X^{-1}(1 − t)/c are written for all c ≥ 0 and t ∈ [0,1] → c = 0 gives the atom at 0 of cZ and no cost, and t = 0 gives zero cost and gain; reason: X_n = c_n Z_n and the empty sum (A10) determine these values; no case is excluded
--   - correction: the ratio (18) tends to 1 with no restriction on the gain → the ratio claim assumes a positive double integral; reason: otherwise the denominator is 0 (for example all costs equal to 0), and only those cases are excluded, from the ratio claim alone
--   - generalization: p. 9 mentions a technical tail condition (6) made "to simplify our proofs" → (6) is not assumed; reason: Assumption 4 imposes only a finite mean on Z, and the statement and proof of Theorem 4 do not use (6); the paper imposes (6) once on p. 9 for all its proofs, so dropping it generalizes the theorem
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), SHA-256 1dfcad7675689de2118550b720b7488b45737ecd5ee5cd6085e5b5d0250d40cd, Theorem 4, p. 16; proof pp. A4–A6, (A10), (A12)

import Mathlib
import Definitions.Def_LargeBSP_Homog_Supplement_Mixture

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LargeBSP.Homog.Supplement

/-- Theorem 4, with the law of C Z at zero costs and the empty-bundle cutoff at t=0.
The ratio clause is conditional only on a positive limiting gain. -/
theorem theorem_4 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ)
    (κ ρ : Measure ℝ) [IsProbabilityMeasure κ] [IsProbabilityMeasure ρ]
    (c : ℕ → ℝ)
    (hZm : ∀ i, Measurable (Z i)) (hZi : iIndepFun Z P)
    (hZlaw : ∀ i, Measure.map (Z i) P = ρ)
    (hρ0 : ρ (Set.Iio 0) = 0) (hρ1 : Integrable id ρ) (hρcont : Continuous (cdf ρ))
    (hκ0 : κ (Set.Iio 0) = 0) (hκ1 : Integrable id κ) (hc : CostRegime c κ) :
    (∀ x : ℝ, cdf (productLaw κ ρ) x = mixtureCdf κ ρ x) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      TendstoInMeasure P (fun N ω => Vbar (fun i => c i * Z i ω) N t) atTop
        (fun _ => Vlim (productLaw κ ρ) t) ∧
      TendstoInMeasure P (fun N ω => cbar c (fun i => c i * Z i ω) N t) atTop
        (fun _ => mixtureCost κ ρ t)) ∧
    (∃ t : ℝ, MaxFraction (fun s => Vlim (productLaw κ ρ) s - mixtureCost κ ρ s) t) ∧
    (∀ t : ℝ, MaxFraction (fun s => Vlim (productLaw κ ρ) s - mixtureCost κ ρ s) t →
      0 < mixtureGain κ ρ t →
      Tendsto (fun N : ℕ => optProfit P (fun i ω => c i * Z i ω) c N /
        ((N : ℝ) * mixtureGain κ ρ t)) atTop (𝓝 1)) := by sorry

end LargeBSP.Homog.Supplement
