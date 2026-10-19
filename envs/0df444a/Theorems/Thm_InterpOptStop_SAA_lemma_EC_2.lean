-- Prove2me | Theorems.Thm_InterpOptStop_SAA_lemma_EC_2
-- name    : InterpOptStop.SAA.lemma_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:48.843674+00:00
-- url     : https://prove2.me/theorems/000c6579-6f5e-4f23-8a12-1fa370c2b724
-- title:
--   Lemma EC.2, pp. ec2–ec3 — |J^{π(·;θ1)}(x̄) − J^{π(·;θ2)}(x̄)| ≤ GT Σ_{s∈splits} f(|θ1,s − θ2,s|)
-- statement:
--   Consider the stopping problem with state space $\mathcal X=\mathcal X_1\times\cdots\times\mathcal X_n$, horizon $T\ge1$, discount factor $\beta\in[0,1]$ and measurable rewards $g(t,\cdot)$. The path has law $\mu$, starts at $\mathbf x(1)=\bar{\mathbf x}$ and lies in $\mathcal X$ almost surely. Assume:
--
--   1. **Assumption 1:** $\mathcal X$ is totally bounded and $\|\mathbf x-\mathbf y\|_\infty\le1$ on $\mathcal X$.
--   2. **Assumption 2:** $0\le g(t,\mathbf x)\le G$ for all $t$ and $\mathbf x\in\mathcal X$.
--   3. **Assumption 3:** $f(0)=0$, $f$ is strictly increasing and continuous on $[0,\infty)$, and $\Pr[\mathbf x(t)\in A]\le f(\lambda(A))$ for measurable $A$ of finite Lebesgue measure and $1<t\le T$.
--
--   Fix a skeleton $(\mathcal T,\mathbf v,\mathbf a)$ and two vectors of split points $\boldsymbol\theta_1,\boldsymbol\theta_2$ such that both tree policies prescribe $\mathbf{go}$ at $\bar{\mathbf x}$. Then
--   $$\Big|J^{\pi(\cdot;\mathcal T,\mathbf v,\boldsymbol\theta_1,\mathbf a)}(\bar{\mathbf x})-J^{\pi(\cdot;\mathcal T,\mathbf v,\boldsymbol\theta_2,\mathbf a)}(\bar{\mathbf x})\Big|\le GT\sum_{s\in\mathbf{splits}}f(|\theta_{1,s}-\theta_{2,s}|).$$
--
--   The value of a tree policy is thus continuous in its split points, with an explicit modulus. This bounds term (a) in the proof of Lemma EC.1.
--
--   **Formalization Note** The page says "Under Assumptions 2 and 3", but its proof uses Assumption 1 for the measure of the slab $A_s$, so Assumption 1 (a standing assumption of §3.4) is a hypothesis here. The page writes "$\boldsymbol\theta_1,\boldsymbol\theta_2\in\mathcal X$". Split points are indexed by splits (eq. (10)), so they are arbitrary vectors in $\mathbb R^{\mathbf{splits}}$. The disclosed readings of the model are: $\beta\in[0,1]$ ("discounted"), $g$ measurable (so the expectation is defined), and the process living in $\mathcal X$. Assumption 3's printed codomain $[0,1]$ for $f$ is dropped: as printed the assumption is unsatisfiable for $n\ge1$, $T\ge2$, and $r\mapsto f(r)+r$ shows the readings are equally strong.
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, Lemma EC.2, pp. ec2–ec3

import Mathlib
import Definitions.Def_InterpOptStop_SAA_StoppingModel
import Definitions.Def_InterpOptStop_SAA_TreePolicy
open MeasureTheory ProbabilityTheory Filter Topology

namespace InterpOptStop.SAA

/-- Lemma EC.2 (arXiv:1812.07211v2, pp. ec2–ec3): two tree policies with the same skeleton that
both continue at `x̄` have values differing by at most `G T Σ_{s ∈ splits} f(|θ₁,s − θ₂,s|)`. -/
theorem lemma_EC_2 {n T : ℕ}
    (hT : 0 < T)
    (xbar : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (Xi : Fin n → Set ℝ) (hXprod : X = Set.univ.pi Xi)
    (hXtb : TotallyBounded X) (hXdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ 1)
    (μ : Measure (Fin T → Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hstart : ∀ᵐ x ∂μ, x ⟨0, hT⟩ = xbar)
    (hinX : ∀ᵐ x ∂μ, ∀ k, x k ∈ X)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (g : Fin T → (Fin n → ℝ) → ℝ) (hgm : ∀ k, Measurable (g k))
    (G : ℝ) (hg : ∀ k, ∀ x ∈ X, 0 ≤ g k x ∧ g k x ≤ G)
    (f : ℝ → ℝ) (hf0 : f 0 = 0) (hfmono : StrictMonoOn f (Set.Ici 0))
    (hfcont : ContinuousOn f (Set.Ici 0))
    (hA3 : ∀ A : Set (Fin n → ℝ), MeasurableSet A → volume A ≠ ⊤ →
      ∀ k : Fin T, (k : ℕ) ≠ 0 → (μ {x | x k ∈ A}).toReal ≤ f (volume A).toReal)
    (S : Tree n) (θ₁ θ₂ : Thresholds) (hgo₁ : policy S θ₁ xbar = Act.go)
    (hgo₂ : policy S θ₂ xbar = Act.go) :
    |J μ β g (policy S θ₁) - J μ β g (policy S θ₂)| ≤
      G * T * ∑ s ∈ S.splits, f |θ₁ s.1 - θ₂ s.1| := by sorry

end InterpOptStop.SAA
