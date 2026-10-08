-- Prove2me | Theorems.Thm_GradSampling_Conv_theorem_3_4
-- name    : GradSampling.Conv.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:48:35.099419+00:00
-- url     : https://prove2.me/theorems/ff37f108-2767-499b-b2d7-503e2dab0c64
-- title:
--   Theorem 3.4, p. 760 — with fixed radius ε, a.s. the GS run stops with ρ_ε = 0 or ρ_ε(xᵏ) →_J 0 with Clarke ε-stationary cluster points
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be locally Lipschitz and continuously differentiable on an open dense set $D$ whose complement has Lebesgue measure zero, and let $\mathcal L=\{x:f(x)\le f(\tilde x)\}$ be compact. Run the GS algorithm from $x^0\in\mathcal L\cap D$ with $\gamma,\beta\in(0,1)$, $\theta\in(0,1]$, $m\ge n+1$, and fixed sampling radius: $\epsilon_0=\epsilon>0$, $\nu_0=0$, $\mu=1$, with samples $u^{kj}$ drawn independently and uniformly from the unit ball. Then, with probability $1$, one of the following holds:
--
--   1. the algorithm terminates at some iteration $k_0$ with $\rho_\epsilon(x^{k_0})=0$; or
--   2. the algorithm never terminates, and there is a subsequence $J\subseteq\mathbb N$ such that
--   $$\rho_\epsilon(x^k)\xrightarrow[k\in J]{}0$$
--   and every cluster point $\bar x$ of $\{x^k\}_{k\in J}$ satisfies $0\in\bar\partial_\epsilon f(\bar x)$.
--
--   This is the main convergence theorem of the paper: for a fixed sampling radius, gradient sampling almost surely produces a Clarke $\epsilon$-stationary point, either at termination or as a cluster point. It does not assert that $\|g^k\|\to0$ along $J$, which the authors leave open.
--
--   **Formalization Note** The hypothesis $\operatorname{vol}(D^c)=0$ is added: the paper's proof uses that Step 1 stops with probability zero, which fails for an open dense $D$ whose complement has positive measure. The run is a `IsRandomGSRun` with $\epsilon_0=\epsilon$, $\nu_0=0$, $\mu=1$; the subsequence $J$ is a strictly increasing $\varphi:\mathbb N\to\mathbb N$, and cluster points are `MapClusterPt`. "With probability 1" is `∀ᵐ ω ∂P`. The paper's event $\mathcal E$ is not used.
-- source:
--   Burke, Lewis, Overton, A robust gradient sampling algorithm for nonsmooth, nonconvex optimization, SIAM J. Optim. 15 (2005), p. 760, Theorem 3.4

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_GradSampling_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace GradSampling.Conv

/-- Theorem 3.4 (convergence for fixed sampling radius), p. 760: run with `ε₀ = ε`, `ν₀ = 0`, `μ = 1`,
with probability 1 the GS algorithm either stops at an iteration `k₀` with `ρ_ε(x^{k₀}) = 0`, or runs
forever and has a subsequence `J` with `ρ_ε(x^k) →_J 0` all of whose cluster points are Clarke
`ε`-stationary. -/
theorem theorem_3_4 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hDo : IsOpen D) (hDd : Dense D)
    (hC1 : ContDiffOn ℝ 1 f D) (hDnull : volume Dᶜ = 0)
    (xt : EuclideanSpace ℝ (Fin n)) (hL : IsCompact (levelSet f xt))
    (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ levelSet f xt ∩ D)
    (γ β : ℝ) (hγ : γ ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1) (θ : ℝ) (hθ : θ ∈ Set.Ioc 0 1)
    (m : ℕ) (hm : n + 1 ≤ m)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (U : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n)) (X : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (eps nu t : ℕ → Ω → ℝ) (g d : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (τ : Ω → ℕ∞)
    (ε : ℝ) (hε : 0 < ε)
    (hrun : IsRandomGSRun P ℱ f D x0 γ β ε 0 1 θ m U X eps nu t g d τ) :
    ∀ᵐ ω ∂P, (∃ k0 : ℕ, τ ω = (k0 : ℕ∞) ∧ rho f D ε (X k0 ω) = 0) ∨
      (τ ω = ⊤ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun i => rho f D ε (X (φ i) ω)) atTop (𝓝 0) ∧
        ∀ xbar, MapClusterPt xbar atTop (fun i => X (φ i) ω) → 0 ∈ epsSubdiff f ε xbar) := by sorry

end GradSampling.Conv
