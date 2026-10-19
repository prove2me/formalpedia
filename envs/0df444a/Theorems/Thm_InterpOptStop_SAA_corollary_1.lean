-- Prove2me | Theorems.Thm_InterpOptStop_SAA_corollary_1
-- name    : InterpOptStop.SAA.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:49.998149+00:00
-- url     : https://prove2.me/theorems/bb725b2b-94f3-4e1e-8774-fa8187fac998
-- title:
--   Corollary 1, p. 10 — a.s. ∃Ω0 ∀Ω ≥ Ω0: |sup_{Πtree(d)} J^π(x̄) − sup_{Πtree(d)} Ĵ^π(x̄)| ≤ ϵ
-- statement:
--   Consider a finite-horizon optimal stopping problem with state $\mathbf x(t)\in\mathcal X=\mathcal X_1\times\cdots\times\mathcal X_n\subseteq\mathbb R^n$, periods $t=1,\dots,T$, starting state $\mathbf x(1)=\bar{\mathbf x}$, discount factor $\beta\in[0,1]$ and measurable stopping rewards $g(t,\mathbf x)$. Assume:
--
--   1. **Assumption 1:** $\mathcal X$ is totally bounded in $\|\cdot\|_\infty$ and $\|\mathbf x-\mathbf y\|_\infty\le1$ on $\mathcal X$.
--   2. **Assumption 2:** $0\le g(t,\mathbf x)\le G$ for all $t$ and $\mathbf x\in\mathcal X$.
--   3. **Assumption 3:** there is $f$ with $f(0)=0$, strictly increasing and continuous on $[0,\infty)$, such that $\Pr[\mathbf x(t)\in A]\le f(\lambda(A))$ for every measurable $A$ of finite Lebesgue measure and every $1<t\le T$.
--
--   Let $J^\pi(\bar{\mathbf x})$ be the expected discounted reward of the stationary policy $\pi$. Let $\hat J^\pi(\bar{\mathbf x})$ be its average discounted reward over the first $\Omega$ of an i.i.d. sequence of trajectories of the process. Fix a finite depth $d$ and $\epsilon>0$. With probability one there is a finite sample size $\Omega_0$ such that for all $\Omega\ge\Omega_0$,
--   $$\Big|\sup_{\pi\in\Pi_{\mathrm{tree}}(d)}J^\pi(\bar{\mathbf x})-\sup_{\pi\in\Pi_{\mathrm{tree}}(d)}\hat J^\pi(\bar{\mathbf x})\Big|\le\epsilon.$$
--
--   The optimal value of the SAA problem over tree policies of depth at most $d$ therefore converges almost surely to the optimal value of the true problem over the same class. This justifies optimizing tree policies on simulated trajectories.
--
--   **Formalization Note** $\Pi_{\mathrm{tree}}(d)$ is the type of (skeleton of depth $\le d$, real split points). The suprema are real suprema over this nonempty type. The values $J^\pi$ lie in $[0,G]$, and so do the values $\hat J^\pi$ on the almost-sure event that the sampled states lie in $\mathcal X$, so both suprema are genuine. The sample is an i.i.d. sequence with the law of the process (disclosed reading of §3.2), and the paper's sample size $\Omega$ is `m`. Further readings: $\beta\in[0,1]$, $g$ measurable, and Assumption 3 for measurable sets of finite Lebesgue measure. The printed codomain $f:[0,\infty)\to[0,1]$ is dropped. As printed, Assumption 3 is unsatisfiable for $n\ge1$, $T\ge2$, since a box containing $\mathcal X$ has probability $1$. The two readings are equally strong, because $r\mapsto f(r)+r$ turns any admissible $[0,1]$-valued $f$ into an admissible one.
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, Corollary 1, p. 10

import Mathlib
import Definitions.Def_InterpOptStop_SAA_StoppingModel
import Definitions.Def_InterpOptStop_SAA_TreePolicy
open MeasureTheory ProbabilityTheory Filter Topology

namespace InterpOptStop.SAA

/-- Corollary 1 (arXiv:1812.07211v2, p. 10): almost surely, the optimal sample-average value over
tree policies of depth at most `d` converges to the optimal true value over the same class. -/
theorem corollary_1 {n T : ℕ}
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
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Fin T → Fin n → ℝ) (hξm : ∀ k, Measurable (ξ k)) (hind : iIndepFun ξ P)
    (hlaw : ∀ k, P.map (ξ k) = μ) :
    ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∀ᵐ ω ∂P, ∃ Ω₀ : ℕ, ∀ m ≥ Ω₀,
      |(⨆ q : TreePol n d, J μ β g (policy q.1.1 q.1.2)) -
          (⨆ q : TreePol n d, Jhat (fun k => ξ k ω) m β g (policy q.1.1 q.1.2))| ≤ ε := by sorry

end InterpOptStop.SAA
