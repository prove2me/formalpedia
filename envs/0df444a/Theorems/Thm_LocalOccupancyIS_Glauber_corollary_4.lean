-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_corollary_4
-- name    : LocalOccupancyIS.Glauber.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:02:13.849549+00:00
-- url     : https://prove2.me/theorems/8b134825-0b6e-47ff-a4a5-b4ec1fe66449
-- title:
--   Corollary 4 and Remark 1 — large sets via ordinary Glauber dynamics
-- statement:
--   Let $G$ be a finite simple graph with $n$ vertices, actual maximum degree $\Delta\ge1$, and hereditary neighborhood $K_{t,t}$-density at most $b\ge0$, where $t\ge1$ is an integer. Use $s=(b+1)^{1/(2t-1)}$, $\rho=\Delta/s$, $D=\log\rho$ and the exact parameters of Proposition 6. For fixed $t$ and sufficiently large $\rho$, with threshold independent of $b$, every fixed neighborhood order gives the two-prefix certificate after two and three sweeps, with zero error and $\kappa\le3\Delta$. From every initial independent set, for every $0<\varepsilon<1$ and integer $T\ge1$,
--
--   $$T\ge\frac{(\beta+3\Delta\max\{\beta p,\gamma\Delta\})^2H_\lambda}{2\varepsilon^2}
--   \ \Longrightarrow\ \mathbb E|I_J|\ge(1-\varepsilon)n/\Gamma.$$
--
--   Here $J$ is independent and uniform on $\{0,\ldots,T-1\}$. The specified largest-visited-set procedure, at $\varepsilon=1/D$ and with independent repetitions, outputs with probability at least $1-\delta$ an independent set satisfying
--
--   $$|I|\ge\left(1-A_t\frac{\log D}{D}\right)\frac{nD}{\Delta},\qquad 0<\delta<1,$$
--
--   in counted time polynomial in $n$ and $\log(1/\delta)$. The finite run and repetition counts, the one-run success lower bound $\varepsilon/(2\Gamma)$ and the sufficient single-run update estimate from pp.19–20 are included. Constants and thresholds precede $b$, graphs, orders, starts and failure probabilities.
--
--   For every parameter sequence with $D\to\infty$ and $t\log D/D\to0$, the same conclusions hold eventually with $A_t=A t$ for one absolute $A$, and with a polynomial exponent independent of $t$. The same absolute scale controls the relative error of $\Gamma D/\Delta$. For fixed $t$, if $\log(b+1)/\log\Delta\to0$, the actual algorithm attains $(1-o(1))n\log\Delta/\Delta$. For $b=0$, this holds on $K_{1,t,t}$-free graphs throughout $t\log\log\Delta/\log\Delta\to0$.
--
--   The separate rational implementation computes a certified midpoint approximation to $x=sD^{2t-1}$ within $1/4$, chooses $x\le q\le x+2\le\Delta+4$ with the sharper eventual bound $q\le\Delta+2$, and uses $\widehat\lambda=1/q$. The certificate and asymptotic estimate use recomputed $p,z,\beta,\gamma$, retaining $c,M,D$. The actual fair-bit machine is normalized, implements independent ordinary-dynamics runs at this rounded fugacity, and succeeds with probability at least $1-e^{-m}$ for every integer $m\ge1$. Its expected charged bit cost is polynomial in $n$, the rational input length and $m$, with absolute exponent in the growing regime. Taking $m\ge\log(1/\delta)$ gives arbitrary desired failure probability. Rejection loops do not receive a deterministic worst-case length bound.
--
--   This is the complete algorithmic independent-set conclusion of Corollary 4 with Remark 1, not an equilibrium sampling assertion.
--
--   Differences from the source:
--   - encoding: arbitrary finite graph vertices and random independent sets → Fin n vertices and published feasible Boolean configurations; reason: every finite source graph has this presentation; point-mass starts cover every source initial state
--   - encoding: fixed-t O_t error, uniform growing-parameter O error and the two o(1) specializations → fixed-t constants and rho threshold before varying input, absolute constants and exponent before all admissible natural-indexed sequences, and eventual assertions for every positive target error; reason: this fixes all uniformities without weakening any leading constant
--   - encoding: retain the largest visited state and repeat independently with the counts of Remark 2 → augmented transition matrices, computed ceilings with at least one step/run, earlier-visit tie breaking and explicit operation charges; reason: the output is always a visited state of these actual reset trajectories; the extra final endpoint can only improve the record
--   - encoding: approximate x within 1/4 and sample the rounded fugacity using random bits in expected polynomial time → rational bisection and normalized log-series enclosures, an explicit first-halting fair-bit machine, n^8 updates and n^3(m+1) independent runs for failure exp(-m); reason: these conservative loop counts eventually dominate the source sufficient counts and preserve its polynomial-time claim; arithmetic, input reading, array operations and rejection are charged
--   - generalization: rational b of polynomial input bit length has expected polynomial bit complexity → an explicit expected bound polynomial in n, the rational bit length, m and the length of t for arbitrary nonnegative rational b in the stated regimes; reason: substituting a polynomial bound on rational input length gives the source claim; reading and processing longer inputs is charged rather than excluded
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), Corollary 4, Remark 1, Remark 2 and proof, p. 6–20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf#page=6

import Definitions.Def_LocalOccupancyIS_Glauber_GoalInterface

namespace LocalOccupancyIS.Glauber
/-- All of Corollary 4 and Remark 1, p.6; implementations pp.19–20.
Absolute constants/exponent precede all varying input sequences. -/
theorem corollary_4 :
    ∃ A B : ℝ, ∃ k : ℕ, 0 < A ∧ 0 < B ∧ 1 ≤ k ∧
    -- Fixed t: the threshold and constants precede b, graph, order and initial state.
    (∀ t : ℕ, 1 ≤ t → ∃ Aₜ Rₜ Bₜ : ℝ, 0 < Aₜ ∧ 1 < Rₜ ∧ 0 < Bₜ ∧
      ∀ n Δ : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
      ∀ b : ℝ, 1 ≤ Δ → 0 ≤ b → MaximumDegree G Δ → HereditaryDensity G t b →
      Rₜ ≤ rho Δ t b → ∀ w : Fin n → List (Fin n),
      (∀ u, IsSweep (G.neighborFinset u) (w u)) → ExactConclusion G Δ t b w Aₜ Bₜ k) ∧
    -- Growing t and b: one absolute error constant and one exponent.
    (∀ (Δ t : ℕ → ℕ) (b : ℕ → ℝ), Admissible Δ t b →
      ∀ᶠ i in Filter.atTop, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
        MaximumDegree G (Δ i) → HereditaryDensity G (t i) (b i) →
        ∀ w : Fin n → List (Fin n), (∀ u, IsSweep (G.neighborFinset u) (w u)) →
          ExactConclusion G (Δ i) (t i) (b i) w (A*t i) B k) ∧
    -- Fixed-t subpolynomial b+1 consequence, with the same actual algorithm.
    (∀ t : ℕ, 1 ≤ t → ∀ (Δ : ℕ → ℕ) (b : ℕ → ℝ),
      (∀ i, 1 ≤ Δ i ∧ 0 ≤ b i) → Filter.Tendsto Δ Filter.atTop Filter.atTop →
      Filter.Tendsto (fun i => Real.log (b i+1)/Real.log (Δ i)) Filter.atTop (nhds 0) →
      ∃ Bₜ : ℝ, 0 < Bₜ ∧ ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in Filter.atTop,
        ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
          MaximumDegree G (Δ i) → HereditaryDensity G t (b i) →
            LeadingOne G (Δ i) t (b i) ζ Bₜ k) ∧
    -- K_{1,t,t}-free throughout t=o(log Δ/log log Δ).
    (∀ (Δ t : ℕ → ℕ), (∀ i, 1 ≤ Δ i ∧ 1 ≤ t i) →
      Filter.Tendsto Δ Filter.atTop Filter.atTop →
      Filter.Tendsto (fun i => (t i:ℝ)*Real.log (Real.log (Δ i))/Real.log (Δ i))
        Filter.atTop (nhds 0) →
      ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in Filter.atTop,
        ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
          MaximumDegree G (Δ i) → ApexFree G (t i) → LeadingOne G (Δ i) (t i) 0 ζ B k) ∧
    -- Rational b: same full mathematical statement, with separately charged expected bit cost.
    (∀ t : ℕ, 1 ≤ t → ∃ Aₜ Rₜ Bₜ : ℝ, 0 < Aₜ ∧ 1 < Rₜ ∧ 0 < Bₜ ∧
      ∀ n Δ : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
      ∀ b : ℚ, 1 ≤ Δ → 0 ≤ b → MaximumDegree G Δ → HereditaryDensity G t b →
      Rₜ ≤ rho Δ t b → ∀ w : Fin n → List (Fin n),
      (∀ u, IsSweep (G.neighborFinset u) (w u)) → BitConclusion G Δ t b w Aₜ Bₜ k) ∧
    (∀ (Δ t : ℕ → ℕ) (b : ℕ → ℚ), Admissible Δ t (fun i => (b i:ℝ)) →
      ∀ᶠ i in Filter.atTop, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
        MaximumDegree G (Δ i) → HereditaryDensity G (t i) (b i) →
        ∀ w : Fin n → List (Fin n), (∀ u, IsSweep (G.neighborFinset u) (w u)) →
          BitConclusion G (Δ i) (t i) (b i) w (A*t i) B k) := by sorry
end LocalOccupancyIS.Glauber
