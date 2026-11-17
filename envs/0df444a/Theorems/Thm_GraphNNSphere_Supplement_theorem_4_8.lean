-- Prove2me | Theorems.Thm_GraphNNSphere_Supplement_theorem_4_8
-- name    : GraphNNSphere.Supplement.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:54:30.806643+00:00
-- url     : https://prove2.me/theorems/f45e5788-0c4f-4360-b5ce-08a2346f5408
-- title:
--   Theorem 4.8, p.49 — enrichment defeats every navigation graph below $\Gamma(\mu,\lambda)$
-- statement:
--   Fix $c>0$, $\beta^*(c)<\beta<1$ and $k\ge1$, and put $d=\lfloor c\log n\rfloor$, $\lambda=1/c$, $\gamma=\beta/c$ and $\Delta=\lceil n^\beta\rceil$. Fix $\mu>0$ and $\kappa>0$ with
--
--   $$\gamma<\Gamma(\mu,\lambda)\qquad\text{and}\qquad \kappa>K_{\mathrm{cap}}(\mu,\lambda).$$
--
--   There are deterministic, everywhere positive two-level densities $f_n\in\mathcal D(\mu,\kappa-\mu)$ with global log-density oscillation at most $\kappa d$ and $\operatorname{ess\,sup}f_n=e^{(\mu+o(1))d}$ such that the following holds for uniform queries $Q_n=\sigma_{d-1}$. With probability $1-e^{-\Omega(d)}$ over $D_n$, simultaneously for every navigation graph with neighbor lists of at most $\Delta$ points, for every query outside a Borel set of measure $e^{-\Omega(d)}$ that may depend on the graph, there is a set of $e^{\Omega(d)}$ failing entries that is disjoint from $\mathrm{Top}_k(q)$ and closed under strictly improving greedy moves: every listed neighbor $y\in G(x)$ of a point $x$ of the set with $\delta(q,y)<\delta(q,x)$ lies in the set. In particular navigation fails from $e^{\Omega(d)}$ entries.
--
--   Sufficiently concentrated high density therefore raises the critical degree above $n^{\beta^*(c)}$ for every graph, even one designed after observing the sample.
--
--   **Formalization Note** "Two-level" means that $f_n$ takes at most two values. Membership in $\mathcal D(\mu,\kappa-\mu)$ is asserted for every admissible slack sequence $\vartheta_d$. The per-$n$ properties hold for all large $n$.
--
--   Differences from the source:
--   - encoding: O(·), o(1), Ω(d), e^{o(d)}, "with probability 1 − o(1)", "for all sufficiently large n" → explicit constants and vanishing sequences in the quantifier order of §2.1 (fixed parameters, constants, d(·), vanishing sequences, ∀ᶠ n), probabilities as measures of explicit measurable events; reason: Lean convention, as in the published goal Theorem 3.1
--   - generalization: f_n ∈ D(µ, κ − µ) for the fixed sequence ϑ_d → f_n ∈ D(µ, κ − µ) for every admissible slack sequence ϑ_d simultaneously; reason: the construction lies in the class without the subexponential slack (p.49); any fixed ϑ_d is one of the sequences covered
--   - reading: per-n properties of f_n (density, positivity, two levels, class, oscillation, ess sup) → for all large n; reason: for small n, d = ⌊c log n⌋ = 0 and no density exists
--   - reading: "closed under strictly improving greedy moves" → every y ∈ G(x) with δ(q, y) < δ(q, x), for x in the set, lies in the set; reason: the proof on p.53 shows exactly this ("An improving neighbor … remains in S(q)"); it implies closure under successor moves
--   - encoding: two-level densities → f_n takes at most two values (∃ a b, ∀ x, f_n(x) = a ∨ f_n(x) = b); reason: the construction (42) takes two values
--   - encoding: ess sup f_n = e^{(µ+o(1))d} → essential supremum in ℝ≥0∞ equal to e^{(µ+ε_n)d}, ε_n → 0; reason: same value
--   - encoding: measurable / Borel query sets → MeasurableSet on the sphere (the subtype of ℝ^d with its Borel σ-algebra); reason: same sets
--   - encoding: failing entry → W_G(q; x₀) = ⊤ in ℕ∞; reason: base mission convention
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 4.8, p.49 (PDF p.51); Γ, K_cap p.49; D(µ+, µ−) p.42; closure from the proof, p.53

import Mathlib
import Definitions.Def_GraphNNSphere_IsNavGraph
import Definitions.Def_GraphNNSphere_maxDeg
import Definitions.Def_GraphNNSphere_IsTarget
import Definitions.Def_GraphNNSphere_W
import Definitions.Def_GraphNNSphere_betaStar
import Definitions.Def_GraphNNSphere_logDim
import Definitions.Def_GraphNNSphere_Supplement_sampleLaw
import Definitions.Def_GraphNNSphere_Supplement_essOscLog
import Definitions.Def_GraphNNSphere_Supplement_DClass
import Definitions.Def_GraphNNSphere_Supplement_GammaCap

open MeasureTheory Filter Topology

namespace GraphNNSphere

namespace Supplement

/-- Theorem 4.8, enrichment and arbitrary navigation graphs (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 4.8, p.49). Let
`d = ⌊c log n⌋`, `β*(c) < β < 1`, `λ = 1/c`, `γ = β/c`, `Δ = ⌈n^β⌉`, `μ, κ > 0` with `γ < Γ(μ, λ)` and
`κ > K_cap(μ, λ)`. There are deterministic, everywhere positive two-level densities `f_n` in
`D(μ, κ - μ)` with global log-density oscillation at most `κd` and `ess sup f_n = e^{(μ+o(1))d}` such that,
for uniform queries, with probability `1 - e^{-Ω(d)}`, simultaneously for every navigation graph with
lists of at most `Δ` points, for every query outside a graph-dependent Borel set of measure
`e^{-Ω(d)}`, a set of `e^{Ω(d)}` failing entries is disjoint from `Top_k(q)` and closed under strictly
improving greedy moves (so navigation fails from `e^{Ω(d)}` entries).

**Formalization Note** "Two-level" is "takes at most two values". Membership in `D(μ, κ - μ)` is
asserted for every admissible slack sequence `ϑ`. Closure under strictly improving moves: every
listed `y ∈ G(x)` with `δ(q, y) < δ(q, x)` of a point `x` of the set lies in the set (p.53). Per-`n`
properties hold for all large `n` (for small `n`, `d = 0`). The essential supremum is taken in
`ℝ≥0∞`. -/
theorem theorem_4_8 :
    ∀ c β : ℝ, 0 < c → betaStar c < β → β < 1 → ∀ k : ℕ, 1 ≤ k → ∀ μ κ : ℝ, 0 < μ → 0 < κ →
      β / c < GammaCap μ (1 / c) → Kcap μ (1 / c) < κ →
      ∃ c₁ c₂ c₃ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧
      ∃ f : ∀ n, Sph (logDim c n) → ℝ, ∃ εs : ℕ → ℝ, Tendsto εs atTop (𝓝 0) ∧
        (∀ᶠ n in atTop, IsDensity (logDim c n) (f n) ∧ (∀ x, 0 < f n x) ∧
          (∃ a b : ℝ, ∀ x, f n x = a ∨ f n x = b) ∧
          (∀ ϑ : ℕ → ℝ, IsSlackSeq ϑ → DClass ϑ (logDim c n) μ (κ - μ) (f n)) ∧
          essOscLog (logDim c n) (f n) Set.univ ≤ ((κ * (logDim c n : ℝ) : ℝ) : EReal) ∧
          essSup (fun x => ENNReal.ofReal (f n x)) (unif (logDim c n)) =
            ENNReal.ofReal (Real.exp ((μ + εs n) * (logDim c n : ℝ)))) ∧
        ∀ᶠ n : ℕ in atTop,
          ∃ E : Set (Fin n → Sph (logDim c n)), MeasurableSet E ∧
            1 - Real.exp (-(c₁ * (logDim c n : ℝ))) ≤ (dataLawF n (logDim c n) (f n) E).toReal ∧
            ∀ X ∈ E, ∀ G : NavGraph n, IsNavGraph G → maxDeg G ≤ ⌈(n : ℝ) ^ β⌉₊ →
              ∃ B : Set (Sph (logDim c n)), MeasurableSet B ∧
                (unif (logDim c n) B).toReal ≤ Real.exp (-(c₂ * (logDim c n : ℝ))) ∧
                ∀ q ∉ B, ∃ S : Finset (Fin n),
                  Real.exp (c₃ * (logDim c n : ℝ)) ≤ (S.card : ℝ) ∧
                  (∀ x ∈ S, ¬ IsTarget k X q x) ∧
                  (∀ x ∈ S, ∀ y ∈ G x, geo q (X y) < geo q (X x) → y ∈ S) ∧
                  (∀ x ∈ S, W G X q k x = ⊤) := by sorry

end Supplement

end GraphNNSphere
