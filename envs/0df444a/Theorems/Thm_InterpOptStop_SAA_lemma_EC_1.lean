-- Prove2me | Theorems.Thm_InterpOptStop_SAA_lemma_EC_1
-- name    : InterpOptStop.SAA.lemma_EC_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:45.384697+00:00
-- url     : https://prove2.me/theorems/f3b31147-ba7e-4f28-ab8c-b9d9c3818bc9
-- title:
--   Lemma EC.1, pp. ec1–ec2 — fixed (𝒯, v, a): a.s. ∃Ω1 ∀Ω ≥ Ω1 ∀θ: |J^{π(·;θ)}(x̄) − Ĵ^{π(·;θ)}(x̄)| ≤ ϵ
-- statement:
--   Consider the stopping problem under Assumptions 1, 2 and 3, with the conventions of the model:
--
--   1. state space $\mathcal X=\mathcal X_1\times\cdots\times\mathcal X_n$;
--   2. horizon $T\ge1$ and discount $\beta\in[0,1]$;
--   3. measurable rewards bounded in $[0,G]$ on $\mathcal X$;
--   4. a path law $\mu$ with $\mathbf x(1)=\bar{\mathbf x}$ and $\mathbf x(t)\in\mathcal X$ almost surely;
--   5. i.i.d. sample trajectories with law $\mu$.
--
--   Fix a skeleton $(\mathcal T,\mathbf v,\mathbf a)$ and $\epsilon>0$. Almost surely, there is a finite $\Omega_1$ such that for all $\Omega\ge\Omega_1$ and all split points $\boldsymbol\theta$,
--   $$\Big|J^{\pi(\cdot;\mathcal T,\mathbf v,\boldsymbol\theta,\mathbf a)}(\bar{\mathbf x})-\hat J^{\pi(\cdot;\mathcal T,\mathbf v,\boldsymbol\theta,\mathbf a)}(\bar{\mathbf x})\Big|\le\epsilon.$$
--
--   This is a uniform strong law over the uncountable family of split points for one skeleton. Theorem 1 follows by taking the maximum over the finitely many skeletons of bounded depth.
--
--   **Formalization Note** The null set and $\Omega_1$ come before "for all $\boldsymbol\theta$", as on the page. The page's "split points $\boldsymbol\theta\in\mathcal X$" is read as all $\boldsymbol\theta\in\mathbb R^{\mathbf{splits}}$ (eq. (10)). This is the stronger reading, and it is still true: split points outside the range of the coordinate over $\mathcal X$ act on $\mathcal X$ like clamped ones. "$\Omega_1\in\mathbb N^+$" adds nothing, because $\Omega_1$ can always be increased. The model readings are: i.i.d. samples, $\beta\in[0,1]$, measurable $g$, and Assumption 3 for measurable sets of finite Lebesgue measure without the printed codomain $[0,1]$ of $f$. As printed, that codomain makes Assumption 3 unsatisfiable for $n\ge1$, $T\ge2$, and $r\mapsto f(r)+r$ shows the two readings are equally strong.
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, Lemma EC.1, pp. ec1–ec2

import Mathlib
import Definitions.Def_InterpOptStop_SAA_StoppingModel
import Definitions.Def_InterpOptStop_SAA_TreePolicy
open MeasureTheory ProbabilityTheory Filter Topology

namespace InterpOptStop.SAA

/-- Lemma EC.1 (arXiv:1812.07211v2, pp. ec1–ec2): for a fixed skeleton `(𝒯, v, a)`, almost
surely the sample-average value converges to the true value uniformly in the split points. -/
theorem lemma_EC_1 {n T : ℕ}
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
    ∀ (S : Tree n) (ε : ℝ), 0 < ε → ∀ᵐ ω ∂P, ∃ Ω₁ : ℕ, ∀ m ≥ Ω₁, ∀ θ : Thresholds,
      |J μ β g (policy S θ) - Jhat (fun k => ξ k ω) m β g (policy S θ)| ≤ ε := by sorry

end InterpOptStop.SAA
