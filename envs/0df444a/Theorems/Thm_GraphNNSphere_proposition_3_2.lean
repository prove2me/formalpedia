-- Prove2me | Theorems.Thm_GraphNNSphere_proposition_3_2
-- name    : GraphNNSphere.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:43:45.808848+00:00
-- url     : https://prove2.me/theorems/9c9da1a2-e97f-4a15-9fbb-b5be2b0e7e80
-- title:
--   Proposition 3.2 — uniform greedy progress
-- statement:
--   Let $r=r_n\in(0,\pi/2)$ and $A=A_n$ with $\theta_1<A<\pi/2$ and $\cos^2A>\cos r$. Put $\tau=(\cos^2A-\cos r)/\sin^2A$, $h=(A-\theta_1)/2$ and $c_{\mathrm{pop}}=d^{-1}\log(nF(A-h))$. Assume $\tau\ge\tau_0$ for a fixed $\tau_0>0$ and that $c_{\mathrm{pop}}$ is bounded below by a positive constant independent of $n$. Fix an absolutely continuous query distribution $Q$ before sampling. For each sample, let $Q_D$ be the measurable set of queries for which both $C(q)$ and $P(q)$ hold, with bisectors excluded. There is a constant $\zeta=\zeta(\tau_0)>0$ such that, for all sufficiently large $n$,
--   $$P_{q\sim Q}(q\in Q_D)\ge1-e^{-\zeta d/2}\quad\text{with probability at least }1-6e^{-\zeta d/2}\text{ over }D_n.$$
--   Let $K=(1-\cos r)/(\cos^2A-\cos r)$ and $H=\lceil(\pi-A)/h\rceil+2\lceil K\rceil+2$. For every $q\in Q_D$, greedy navigation on every graph $G$ containing $G_r$ succeeds from every entry within $H$ complete expansions, using at most $H$ moves and evaluation cost at most $1+H\Delta(G)$.
--
--   This is the engine of the upper bound: it turns conditions on a radius $r$ into progress on every graph that retains the edges of $G_r$.
--
--   Differences from the source:
--   - reading: ζ = ζ(τ₀); sufficiently large n → ζ depends on τ₀ only, and comes before k, d, r, A, c₀ and Q; the threshold on n may depend on k and the sequences but not on Q; reason: the convention of §2.1 and the stronger reading; the failure bound is uniform in the fixed query
--   - encoding: "with probability at least" → an explicit measurable data event E, with the bound for each X ∈ E; reason: so that no outer measure is involved
--   - encoding: hypotheses on r, A, τ, c_pop for the sequences → hypotheses holding eventually in n, with c_pop ≥ c₀ > 0; reason: the statement concerns large n
--   - encoding: labels identified with points → the deterministic clause holds for every X, including samples with repeated points; reason: repeated points have probability zero, and the labels carry the same run
--   - encoding: the listed point closest to q → minimum by (distance, label); reason: a tie is possible only among equidistant points; Q_D excludes bisectors of distinct points
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Proposition 3.2, p.20

import Mathlib
import Definitions.Def_GraphNNSphere_theta1
import Definitions.Def_GraphNNSphere_dataLaw
import Definitions.Def_GraphNNSphere_StandingAsymp
import Definitions.Def_GraphNNSphere_goodQueries
import Definitions.Def_GraphNNSphere_IsNavGraph
import Definitions.Def_GraphNNSphere_Contains
import Definitions.Def_GraphNNSphere_maxDeg
import Definitions.Def_GraphNNSphere_greedyRun

open MeasureTheory Filter

namespace GraphNNSphere

/-- Proposition 3.2, uniform greedy progress (Lu, *Sharp Limits of Graph-Based Nearest Neighbor
Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Proposition 3.2, p.20).

**Formalization Note** `r`, `A` are sequences, with `h = (A - θ₁)/2`,
`c_pop = d⁻¹ log(n F(A - h))`, `τ`, `K` and `H` written out. The constant `ζ = ζ(τ₀)` depends only on
`τ₀`, and comes before `k`, `d`, `r`, `A` and `Q`; the threshold on `n` may depend on the sequences
but not on `Q`. `goodQueries` is the set `Q_D`, and its measurability is a clause. -/
theorem proposition_3_2 (τ₀ : ℝ) (hτ₀ : 0 < τ₀) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ k : ℕ, 1 ≤ k →
      ∀ d : ℕ → ℕ, StandingAsymp d → ∀ (r A : ℕ → ℝ) (c₀ : ℝ), 0 < c₀ →
      (∀ᶠ n : ℕ in atTop,
        0 < r n ∧ r n < Real.pi / 2 ∧ theta1 n (d n) < A n ∧ A n < Real.pi / 2 ∧
        Real.cos (r n) < Real.cos (A n) ^ 2 ∧
        τ₀ ≤ (Real.cos (A n) ^ 2 - Real.cos (r n)) / Real.sin (A n) ^ 2 ∧
        c₀ ≤ (d n : ℝ)⁻¹ *
          Real.log ((n : ℝ) * capMass (d n) (A n - (A n - theta1 n (d n)) / 2))) →
      ∀ᶠ n : ℕ in atTop,
        let h : ℝ := (A n - theta1 n (d n)) / 2
        let K : ℝ := (1 - Real.cos (r n)) / (Real.cos (A n) ^ 2 - Real.cos (r n))
        let H : ℕ := ⌈(Real.pi - A n) / h⌉₊ + 2 * ⌈K⌉₊ + 2
        (∀ X : Fin n → Sph (d n), MeasurableSet (goodQueries k X (A n) (r n) h)) ∧
        (∀ Q : Measure (Sph (d n)), IsProbabilityMeasure Q → Q ≪ unif (d n) →
          ∃ E : Set (Fin n → Sph (d n)), MeasurableSet E ∧
            1 - 6 * Real.exp (-(ζ * (d n : ℝ) / 2)) ≤ (dataLaw n (d n) E).toReal ∧
            ∀ X ∈ E, 1 - Real.exp (-(ζ * (d n : ℝ) / 2)) ≤
              (Q (goodQueries k X (A n) (r n) h)).toReal) ∧
        (∀ X : Fin n → Sph (d n), ∀ q ∈ goodQueries k X (A n) (r n) h, ∀ G : NavGraph n,
          IsNavGraph G → Contains G (thresholdGraph X (r n)) → ∀ x₀ : Fin n,
          ∃ moves expansions evals : ℕ,
            greedyRun G X q k x₀ = .success moves expansions evals ∧
            expansions ≤ H ∧ moves ≤ H ∧ evals ≤ 1 + H * maxDeg G) := by sorry

end GraphNNSphere
