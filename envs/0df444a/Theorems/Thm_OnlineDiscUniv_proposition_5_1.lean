-- Prove2me | Theorems.Thm_OnlineDiscUniv_proposition_5_1
-- name    : OnlineDiscUniv.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:24.371011+00:00
-- url     : https://prove2.me/theorems/8464e02f-49a9-48a8-afcf-eef85a71cd56
-- title:
--   Proposition 5.1 — tightness of the empirical path measures, admissibility of their limits, and $\liminf\inf_{\varepsilon}\mathbb E_\mu D_{M,N}\ge R_\alpha$
-- statement:
--   Assume that the coordinate law $\mu$ has mean zero, unit variance and a finite fourth moment. For every sequence of randomized online algorithms and every sequence $M/N\to\alpha$, the laws of the random empirical measures $\widehat\nu_N$ of the Doob paths (5.1) are tight in $\mathcal P(\mathcal P(\mathcal C^2))$, with weak convergence at both levels. Every limit $Q$ is supported on measures $m$ under which the canonical processes $(A,B)$ satisfy
--   $$
--   A_t=\int_0^ta_s\,ds,\qquad0\le t\le1,\qquad(5.2)
--   $$
--   where $B$ is a Brownian motion in the canonical joint filtration, $a$ is progressively measurable, and
--   $$
--   \mathbb E_ma_t^2\le\frac{2}{\pi\alpha}=c_\alpha^2\quad\text{for a.e. }t\in[0,1].\qquad(5.3)
--   $$
--   In addition,
--   $$
--   \liminf_{M/N\to\alpha}\ \inf_{\varepsilon\text{ online}}\mathbb E_\mu D_{M,N}\ge R_\alpha.\qquad(5.4)
--   $$
--
--   This is the compactness step of the lower bound: every online algorithm is asymptotically a Brownian control with budget $c_\alpha$.
--
--   Differences from the source:
--   - generalization: a fixed standard Brownian motion B with its completed natural filtration → every process B with IsBrownianReal B P on every probability space, the values computed on that B; reason: the Brownian control values depend only on the law of B; the source's Brownian motion is one such process
--   - reading: inf / sup over randomized online algorithms (seed space unspecified) → inf / sup over every seed space S : Type with a σ-algebra, every seed probability law and every jointly measurable causal sign map; reason: the paper fixes no seed space; quantifying over all of them is the stronger reading of both the lower and the upper bound
--   - encoding: ε_k = A_{k,M,N}(U, ξ_1, …, ξ_k) ∈ {−1,+1} → sign maps jointly measurable in (seed, input), constant in columns after k; reason: measurability is implicit in the paper (probabilities and expectations of D_{M,N} must be defined); causality is the online constraint
--   - encoding: µ has mean zero, variance one and a finite fourth moment → IsProbabilityMeasure µ, Integrable x⁴, ∫ x dµ = 0, ∫ x² dµ = 1; reason: x⁴ integrable implies x and x² integrable for a probability law, so the Bochner integrals are the true moments
--   - encoding: M/N → α (M = M_N) → every integer sequence Mseq with Mseq N / N → α; reason: the paper's standing convention of §2.1
--   - encoding: C² = C([0,1], ℝ)²; P(E) the Borel probability measures with weak convergence → C([0,1], ℝ²) with its Borel σ-algebra; Mathlib's ProbabilityMeasure with the weak topology and the Giry σ-algebra; laws as image measures; tightness of the set of laws; reason: C([0,1],ℝ)² and C([0,1],ℝ²) are homeomorphic; on a Polish space the Giry σ-algebra of P(E) is its Borel σ-algebra
--   - reading: "its law is therefore an element of P(P(C²))" → the conclusion includes a.e.-measurability of ν̂_N; reason: the paper treats ν̂_N as a random element of P(C²); the claim makes its law well defined
--   - reading: every limit Q is supported on measures m …; the canonical joint filtration → every subsequential limit Q (convergence of ∫f for all bounded continuous f) gives mass one to a measurable set of admissible laws; the uncompleted canonical filtration; reason: limits of a tight sequence are subsequential limits; "supported on" as a measurable set of full measure; the paper does not say completed here
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Proposition 5.1, (5.1)–(5.4), pp.23–24 (PDF pp.24–25)

import Mathlib
import Definitions.Def_OnlineDiscUniv_Ralpha
import Definitions.Def_OnlineDiscUniv_optDisc
import Definitions.Def_OnlineDiscUniv_empPathMeas
import Definitions.Def_OnlineDiscUniv_IsAdmLimitLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace OnlineDiscUniv

/-- **Proposition 5.1** (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…, printed p.24,
PDF p.25). Assume that the coordinate law has mean zero, unit variance, and a finite fourth
moment. For every sequence of randomized online algorithms and every sequence `M/N → α`, the laws
of `ν̂_N` are tight in `P(P(C²))`, with weak convergence at both levels. Every limit `Q` is
supported on measures `m` under which the canonical processes `(A, B)` satisfy `A_t = ∫_0^t a_s ds`
(5.2), where `B` is a Brownian motion in the canonical joint filtration, `a` is progressively
measurable, and `E_m a_t² ≤ 2/(πα) = c_α²` for a.e. `t ∈ [0,1]` (5.3). In addition,
`liminf_{M/N→α} inf_{ε online} E_μ D_{M,N} ≥ R_α` (5.4).

**Formalization Note** The algorithm sequence is arbitrary: one seed space `Sq N : Type`, seed law
and online algorithm for each `N`. `ν̂_N` is `empPathMeas`, the empirical measure of the
interpolated Doob paths (5.1) for the filtration `σ(U, ξ_1, …, ξ_k)`; it is a random element of
`P(C([0,1], ℝ²))` (`C²` encoded as `C([0,1], ℝ²)`) and is claimed to be a.e.-measurable, so that its
law is a probability measure on `P(C²)`. `P(C²)` carries the topology of weak convergence and the
Giry σ-algebra (which is its Borel σ-algebra, `C²` being Polish). "Limit" means a subsequential
limit: convergence of `∫ f` for every bounded continuous `f` on `P(C²)`. "Supported on" means a
measurable set of admissible laws (`IsAdmLimitLaw`, uncompleted canonical filtration) of
`Q`-measure one. (5.4) is a `liminf` in `ℝ≥0∞` over the class of `optDisc`. -/
theorem proposition_5_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (α : ℝ) (hα : 0 < α)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (h4 : Integrable (fun x : ℝ => x ^ 4) μ)
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1) (Mseq : ℕ → ℕ)
    (hM : Tendsto (fun N : ℕ => (Mseq N : ℝ) / N) atTop (𝓝 α))
    (Sq : ℕ → Type) [∀ N, MeasurableSpace (Sq N)] (ρ : ∀ N, Measure (Sq N))
    [∀ N, IsProbabilityMeasure (ρ N)] (alg : ∀ N, OnlineAlg (Sq N) (Mseq N) N) :
    (∀ N, AEMeasurable (empPathMeas μ (ρ N) (alg N)) ((ρ N).prod (inputLaw μ (Mseq N) N))) ∧
    IsTightMeasureSet (Set.range fun N =>
      ((ρ N).prod (inputLaw μ (Mseq N) N)).map (empPathMeas μ (ρ N) (alg N))) ∧
    (∀ φ : ℕ → ℕ, StrictMono φ → ∀ Q : Measure (ProbabilityMeasure C(unitInterval, ℝ × ℝ)),
      IsProbabilityMeasure Q →
      (∀ f : BoundedContinuousFunction (ProbabilityMeasure C(unitInterval, ℝ × ℝ)) ℝ,
        Tendsto (fun n => ∫ m, f m ∂(((ρ (φ n)).prod (inputLaw μ (Mseq (φ n)) (φ n))).map
          (empPathMeas μ (ρ (φ n)) (alg (φ n))))) atTop (𝓝 (∫ m, f m ∂Q))) →
      ∃ T : Set (ProbabilityMeasure C(unitInterval, ℝ × ℝ)), MeasurableSet T ∧
        T ⊆ {m | IsAdmLimitLaw α m} ∧ Q T = 1) ∧
    Ralpha P B α ≤ liminf (fun N : ℕ => optDisc μ (Mseq N) N) atTop := by sorry

end OnlineDiscUniv
