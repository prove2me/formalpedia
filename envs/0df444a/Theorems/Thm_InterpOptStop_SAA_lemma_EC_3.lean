-- Prove2me | Theorems.Thm_InterpOptStop_SAA_lemma_EC_3
-- name    : InterpOptStop.SAA.lemma_EC_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:40.056506+00:00
-- url     : https://prove2.me/theorems/6373bcb6-0513-4668-b095-950d55648972
-- title:
--   Lemma EC.3, pp. ec3–ec4 — |Ĵ^{π(·;θ1)}(x̄) − Ĵ^{π(·;θ2)}(x̄)| ≤ (G/Ω) Σ_ω Σ_{t≠1} Σ_s 𝕀{x_{v(s)}(ω,t) ∈ [min, max]}
-- statement:
--   This is a deterministic statement about any finite sample. Let $\beta\in[0,1]$ and let $0\le g(t,\mathbf x)\le G$ for all $t$ and $\mathbf x\in\mathcal X$ (Assumption 2). Let $\mathbf x(\omega,\cdot)$, $\omega=1,\dots,\Omega$, be trajectories that start at $\mathbf x(\omega,1)=\bar{\mathbf x}$ and stay in $\mathcal X$. Fix a skeleton $(\mathcal T,\mathbf v,\mathbf a)$ and split points $\boldsymbol\theta_1,\boldsymbol\theta_2$ such that both tree policies prescribe $\mathbf{go}$ at $\bar{\mathbf x}$. Then
--   $$\Big|\hat J^{\pi(\cdot;\mathcal T,\mathbf v,\boldsymbol\theta_1,\mathbf a)}(\bar{\mathbf x})-\hat J^{\pi(\cdot;\mathcal T,\mathbf v,\boldsymbol\theta_2,\mathbf a)}(\bar{\mathbf x})\Big|\le\frac G\Omega\sum_{\omega=1}^{\Omega}\sum_{t\in[T]\setminus\{1\}}\sum_{s\in\mathbf{splits}}\mathbb I\big\{x_{v(s)}(\omega,t)\in[\min\{\theta_{1s},\theta_{2s}\},\max\{\theta_{1s},\theta_{2s}\}]\big\}.$$
--
--   The sample-average value of a tree policy can therefore change only through sample states that fall in the slabs between the two thresholds. This bounds term (c) in the proof of Lemma EC.1.
--
--   **Formalization Note** The trajectories are the first $m$ entries of a sequence `ys`, the paper's $\Omega$ is `m`, and periods are 0-indexed ($t\ne1$ is `j ≠ 0`). The hypotheses $\mathbf x(\omega,1)=\bar{\mathbf x}$ (§3.2) and $\mathbf x(\omega,t)\in\mathcal X$ (Assumption 2 bounds $g$ only on $\mathcal X$) are stated for those $m$ trajectories. The printed indicator omits "$(\omega,t)$", which the proof's last line has. The page's "$\boldsymbol\theta_1,\boldsymbol\theta_2\in\mathcal X$" is read as arbitrary split-point vectors. At $m=0$ both sides are $0$.
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, Lemma EC.3, pp. ec3–ec4

import Mathlib
import Definitions.Def_InterpOptStop_SAA_StoppingModel
import Definitions.Def_InterpOptStop_SAA_TreePolicy
open MeasureTheory ProbabilityTheory Filter Topology

namespace InterpOptStop.SAA

/-- Lemma EC.3 (arXiv:1812.07211v2, pp. ec3–ec4): a deterministic bound, for any `m` trajectories
started at `x̄` and lying in `𝒳`, on the difference of the sample-average values of two tree
policies with the same skeleton that both continue at `x̄`. -/
theorem lemma_EC_3 {n T : ℕ}
    (hT : 0 < T)
    (xbar : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (Xi : Fin n → Set ℝ) (hXprod : X = Set.univ.pi Xi)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (g : Fin T → (Fin n → ℝ) → ℝ)
    (G : ℝ) (hg : ∀ k, ∀ x ∈ X, 0 ≤ g k x ∧ g k x ≤ G) :
    ∀ (ys : ℕ → Fin T → Fin n → ℝ) (m : ℕ), (∀ k < m, ys k ⟨0, hT⟩ = xbar) →
      (∀ k < m, ∀ j, ys k j ∈ X) →
      ∀ (S : Tree n) (θ₁ θ₂ : Thresholds), policy S θ₁ xbar = Act.go →
      policy S θ₂ xbar = Act.go →
      |Jhat ys m β g (policy S θ₁) - Jhat ys m β g (policy S θ₂)| ≤
        G / m * ∑ k ∈ Finset.range m, ∑ j ∈ Finset.univ.filter (fun j : Fin T => (j : ℕ) ≠ 0),
          ∑ s ∈ S.splits, (Set.uIcc (θ₁ s.1) (θ₂ s.1)).indicator (fun _ => (1 : ℝ)) (ys k j s.2) := by sorry

end InterpOptStop.SAA
