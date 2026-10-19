-- Prove2me | Theorems.Thm_InterpOptStop_SAA_fixed_policy_slln
-- name    : InterpOptStop.SAA.fixed_policy_slln
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:50.698306+00:00
-- url     : https://prove2.me/theorems/0a78fa5a-d522-47e5-bf36-f810c15a12c9
-- title:
--   EC.1.1, first paragraph, p. ec1 — for a fixed tree policy π, Ĵ^π(x̄) → J^π(x̄) almost surely
-- statement:
--   Let the path have law $\mu$ and lie in $\mathcal X$ almost surely, let $\beta\in[0,1]$, let the rewards $g(t,\cdot)$ be measurable with $0\le g\le G$ on $\mathcal X$ (Assumption 2), and let $\mathbf x(1,\cdot),\mathbf x(2,\cdot),\dots$ be independent trajectories, each with law $\mu$. For every fixed tree policy $\pi=\pi(\cdot;\mathcal T,\mathbf v,\boldsymbol\theta,\mathbf a)$, almost surely
--   $$\hat J^{\pi}(\bar{\mathbf x})=\frac1\Omega\sum_{\omega=1}^{\Omega}\beta^{\tau_{\pi,\omega}-1}g\big(\tau_{\pi,\omega},\mathbf x(\omega,\tau_{\pi,\omega})\big)\ \longrightarrow\ J^{\pi}(\bar{\mathbf x})\qquad(\Omega\to\infty).$$
--
--   This is the strong law of large numbers applied to one policy. The difficulty of Theorem 1 is that it must hold simultaneously for uncountably many policies.
--
--   **Formalization Note** The sample is an i.i.d. sequence `ξ k : Ω → (paths)` on a probability space `(Ω, P)`: measurable, mutually independent (`iIndepFun`), each with law `μ`. This is a disclosed reading, since §3.2 says only "trajectories of the process" and the proof invokes the strong law. The page writes "$J^\pi(\bar{\mathbf x})\to\hat J^\pi(\bar{\mathbf x})$". The limit is taken in the sample size, so the statement is $\hat J\to J$. It is stated for tree policies, which is how the proof uses it, because an arbitrary map $\pi:\mathcal X\to A$ need not be measurable.
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, §EC.1.1, first paragraph, p. ec1 ("via the strong law of large numbers, J^π(x̄) → Ĵ^π(x̄) almost surely for a fixed policy π")

import Mathlib
import Definitions.Def_InterpOptStop_SAA_StoppingModel
import Definitions.Def_InterpOptStop_SAA_TreePolicy
open MeasureTheory ProbabilityTheory Filter Topology

namespace InterpOptStop.SAA

/-- EC.1.1, first paragraph (arXiv:1812.07211v2, p. ec1): for a fixed tree policy, the
sample-average value converges almost surely to the true value (strong law of large numbers). -/
theorem fixed_policy_slln {n T : ℕ}
    (X : Set (Fin n → ℝ)) (Xi : Fin n → Set ℝ) (hXprod : X = Set.univ.pi Xi)
    (μ : Measure (Fin T → Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hinX : ∀ᵐ x ∂μ, ∀ k, x k ∈ X)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (g : Fin T → (Fin n → ℝ) → ℝ) (hgm : ∀ k, Measurable (g k))
    (G : ℝ) (hg : ∀ k, ∀ x ∈ X, 0 ≤ g k x ∧ g k x ≤ G)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Fin T → Fin n → ℝ) (hξm : ∀ k, Measurable (ξ k)) (hind : iIndepFun ξ P)
    (hlaw : ∀ k, P.map (ξ k) = μ) :
    ∀ (S : Tree n) (θ : Thresholds), ∀ᵐ ω ∂P,
      Tendsto (fun m : ℕ => Jhat (fun k => ξ k ω) m β g (policy S θ)) atTop
        (𝓝 (J μ β g (policy S θ))) := by sorry

end InterpOptStop.SAA
