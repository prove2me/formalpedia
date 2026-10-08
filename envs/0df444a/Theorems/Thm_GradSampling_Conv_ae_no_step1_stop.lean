-- Prove2me | Theorems.Thm_GradSampling_Conv_ae_no_step1_stop
-- name    : GradSampling.Conv.ae_no_step1_stop
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:48:23.679006+00:00
-- url     : https://prove2.me/theorems/98f78633-dca9-48c2-8abf-030abd034f4d
-- title:
--   Proof of Theorem 3.4, p. 760 — with probability 1 the GS algorithm does not terminate in Step 1
-- statement:
--   Assume the standing hypotheses: $f$ is locally Lipschitz, $D$ is open and dense, $f$ is continuously differentiable on $D$, $\mathcal L$ is compact, $x^0\in\mathcal L\cap D$, $\gamma,\beta\in(0,1)$, $\theta\in(0,1]$, $m\ge n+1$, and $D^{c}$ has Lebesgue measure zero. Let $\epsilon_0>0$, $\nu_0\ge0$, $\mu\in(0,1]$, and let $(x^k,\epsilon_k,\nu_k,t_k,g^k,d^k,\tau)$ be a random GS run on $(\Omega,P)$. Then almost surely
--
--   $$x^k+\epsilon_k u^{kj}\in D\qquad\text{for every iteration }k\le\tau\text{ and every }j=1,\dots,m,$$
--
--   so the algorithm never stops in Step 1.
--
--   **Formalization Note** The hypothesis $\operatorname{vol}(D^c)=0$ is added. The paper's proof says "the probability that $x+\epsilon z\notin D$ is zero", which needs it; an open dense set can have a complement of positive measure.
-- source:
--   Burke, Lewis, Overton, A robust gradient sampling algorithm for nonsmooth, nonconvex optimization, SIAM J. Optim. 15 (2005), p. 760, proof of Theorem 3.4, second paragraph (also p. 757 and the proof of Theorem 3.8, p. 765)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_GradSampling_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace GradSampling.Conv

/-- Proof of Theorem 3.4, p. 760: with probability 1 the GS algorithm never stops in Step 1, i.e. every
sampling point `x^k + ε_k u^{kj}` of every iteration `k ≤ τ` lies in `D`. -/
theorem ae_no_step1_stop {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f)
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
    (ε0 ν0 μ : ℝ) (hε0 : 0 < ε0) (hν0 : 0 ≤ ν0) (hμ : μ ∈ Set.Ioc 0 1)
    (hrun : IsRandomGSRun P ℱ f D x0 γ β ε0 ν0 μ θ m U X eps nu t g d τ) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, (k : ℕ∞) ≤ τ ω → ∀ j, X k ω + eps k ω • U k j ω ∈ D := by sorry

end GradSampling.Conv
