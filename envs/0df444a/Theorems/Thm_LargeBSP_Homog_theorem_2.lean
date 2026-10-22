-- Prove2me | Theorems.Thm_LargeBSP_Homog_theorem_2
-- name    : LargeBSP.Homog.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:55.922963+00:00
-- url     : https://prove2.me/theorems/56062929-985e-4ab8-8c0e-fb1b8c076bac
-- title:
--   Theorem 2, p. 12 — identical costs c ≥ 0: V̄_N(t) ⇒ ∫_0^t F_X^{-1}(1−s)ds, c̄_N(t) ⇒ tc, t⋆ = sup{s : F_X^{-1}(1−s) ≥ c}, lim E[π(p⋆_N)]/PPD = 1
-- statement:
--   Work in the large-offering regime: a customer's valuations $X_1, X_2, \dots \ge 0$ are random variables whose empirical distribution functions satisfy $\mathbb F_{X,N}(x) \Rightarrow F_X(x)$ for every $x \ge 0$ (Assumption 1), where $F_X$ is the distribution function of a nonnegative random variable with finite mean $\mu$; $\{X_n\}$ is uniformly integrable and $\frac1N \sum_{n=1}^N X_n \Rightarrow \mu$ (Assumption 2). All marginal costs equal $c \ge 0$. Then, as $N \to \infty$:
--
--   1. for every $t \in [0,1]$,
--   $$\bar V_N(t) \Rightarrow \bar V(t) = \int_0^t F_X^{-1}(1-s)\,ds;$$
--   2. for every $t \in [0,1]$, $\bar c_N(t) \Rightarrow \bar c(t) = t\,c$;
--   3. $t^\star = \sup\{ s \in (0,1) : F_X^{-1}(1-s) \ge c\}$ lies in $[0,1]$ and maximizes $\bar V(t) - t c$ over $t \in [0,1]$ (so it is the $t^\star$ of Theorem 1), and if $c$ is a continuity point of $F_X$ then $t^\star = 1 - F_X(c)$;
--   4. if $F_X(c) < 1$, the optimal expected BSP profit attains perfect price discrimination asymptotically:
--   $$\lim_{N\to\infty} \frac{\mathbb E[\pi(p^\star_N)]}{\mathrm{PPD}} = 1,$$
--   where $\mathbb E[\pi(p^\star_N)]$ is the supremum of the expected profit over all menus of bundle-size prices in $\mathbb R_+ \cup \{\infty\}$ with $N$ products and $\mathrm{PPD} = \sum_{n=1}^N \mathbb E[(X_n - c)^+]$.
--
--   This is the paper's headline result: with identical marginal costs, pricing by bundle size alone loses nothing, to first order, against perfect price discrimination.
--
--   **Formalization Note** $\Rightarrow$ toward a constant is convergence in probability (for $\bar c_N$, which is deterministic here, convergence in probability toward $tc$ is ordinary convergence). Valuations are one sequence, the $N$-product model using its first $N$ terms; they are measurable and nonnegative ($F_X$ is the law of a nonnegative variable and the quantile is an infimum over $x \ge 0$). $F_X$ is `cdf ν` for a probability measure `ν` on $\mathbb R$ with $\nu(-\infty,0) = 0$ and finite mean. The hypothesis $F_X(c) < 1$ on the fourth claim is a disclosed addition: when $F_X(c) = 1$ we have $\mathrm{PPD}/N \to 0$, the ratio is $0/0$ whenever every $X_n \le c$, and its limit is not determined by the assumptions; $F_X(c) < 1$ is exactly the condition that PPD grows linearly in $N$. The set defining $t^\star$ is taken over $(0,1)$, where $F_X^{-1}$ is defined; the page writes $[0,1]$, with the same supremum. The customer's choice breaks ties toward the smaller size, so an indifferent customer does not buy; $\mathbb E[\pi(p^\star_N)]$ is therefore a supremum over menus, not an attained maximum.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), Theorem 2, p. 12

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeBSP.Homog

/-- Theorem 2, p. 12: with identical marginal costs `c ≥ 0`, in the large-offering regime,
(i) `V̄_N(t) ⇒ V̄(t) = ∫_0^t F_X⁻¹(1 − s) ds` and (ii) `c̄_N(t) ⇒ t c` for `t ∈ [0,1]`;
(iii) `t⋆ = sup {s : F_X⁻¹(1 − s) ≥ c}` lies in `[0,1]` and maximizes `V̄(t) − t c` there, and
equals `1 − F_X(c)` when `c` is a continuity point of `F_X`; (iv) `E[π(p⋆_N)]/PPD → 1`
(when `F_X(c) < 1`, i.e. PPD grows linearly). -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν)
    (hA1 : ∀ y : ℝ, 0 ≤ y → TendstoInMeasure P
      (fun (N : ℕ) ω => empCdf (fun n => X n ω) N y) atTop (fun _ => cdf ν y))
    (hUI : UniformIntegrable X 1 P)
    (hWLLN : TendstoInMeasure P (fun (N : ℕ) ω => (∑ n ∈ Finset.range N, X n ω) / N) atTop
      (fun _ => ∫ y, y ∂ν))
    (c : ℝ) (hc : 0 ≤ c) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure P
      (fun (N : ℕ) ω => Vbar (fun n => X n ω) N t) atTop (fun _ => Vlim ν t)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure P
      (fun (N : ℕ) ω => cbar (fun _ => c) (fun n => X n ω) N t) atTop (fun _ => t * c)) ∧
    (tstar ν c ∈ Set.Icc (0 : ℝ) 1 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Vlim ν t - t * c ≤ Vlim ν (tstar ν c) - tstar ν c * c) ∧
      (ContinuousAt (cdf ν) c → tstar ν c = 1 - cdf ν c)) ∧
    (cdf ν c < 1 →
      Tendsto (fun N : ℕ => optProfit P X (fun _ => c) N / PPD P X (fun _ => c) N) atTop
        (𝓝 1)) := by sorry

end LargeBSP.Homog
