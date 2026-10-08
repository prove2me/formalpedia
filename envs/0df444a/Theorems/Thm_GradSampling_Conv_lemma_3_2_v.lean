-- Prove2me | Theorems.Thm_GradSampling_Conv_lemma_3_2_v
-- name    : GradSampling.Conv.lemma_3_2_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:48:25.272599+00:00
-- url     : https://prove2.me/theorems/bfaa5d84-7c97-4cf6-978d-56e01bf18426
-- title:
--   Lemma 3.2(v), p. 759 — finite cover of a compact K ⊂ ℒ with ρ_ε ≥ η by balls z^j + τ_j int 𝔹, τ_j < ε/3, with uniform μ̄-boxes in V_ε
-- statement:
--   Let $D$ be open and dense, $f$ continuously differentiable on $D$, $\epsilon,\delta,\eta>0$, $m\ge n+1$, and let $K\subseteq\mathcal L$ be a nonempty compact set with $\rho_\epsilon(x)\ge\eta$ for all $x\in K$. Then there exist $\bar\mu>0$, an integer $\ell\ge1$, radii $\tau_j\in(0,\epsilon/3)$ and points $z^1,\dots,z^\ell\in K$ such that
--
--   $$K\subseteq\bigcup_{j=1}^{\ell}\big(z^j+\tau_j\operatorname{int}\mathbb B\big),$$
--
--   and for each $j$ there is a tuple $(z^{j1},\dots,z^{jm})\in V_\epsilon(z^j,z^j,\delta)$ with
--
--   $$(z^{j1},\dots,z^{jm})+\bar\mu\,\mathbb B^m\subseteq V_\epsilon(z^j,x,\delta)\qquad\text{whenever }x\in z^j+\tau_j\mathbb B .$$
--
--   Here $(z^{j1},\dots,z^{jm})+\bar\mu\mathbb B^m$ is the set of tuples $(y^1,\dots,y^m)$ with $\|y^i-z^{ji}\|\le\bar\mu$ for every $i$. This uniform positive-volume target is what the random samples hit infinitely often in the proof of Theorem 3.4.
--
--   **Formalization Note** $\inf_K\rho_\epsilon\ge\eta$ is written pointwise, without an infimum. Nonemptiness of $K$ is added: for $K=\emptyset$ no $\ell\ge1$ points of $K$ exist; in the application $K$ contains the iterates.
-- source:
--   Burke, Lewis, Overton, A robust gradient sampling algorithm for nonsmooth, nonconvex optimization, SIAM J. Optim. 15 (2005), p. 759, Lemma 3.2(v) (preamble on p. 758)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_GradSampling_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace GradSampling.Conv

/-- Lemma 3.2(v), p. 759: a finite cover of a compact `K ⊆ ℒ` with `ρ_ε ≥ η` on `K` by balls
`z^j + τ_j int 𝔹`, `τ_j ∈ (0, ε/3)`, with tuples `(z^{j1}, …, z^{jm}) ∈ V_ε(z^j, z^j, δ)` whose
`μ̄`-neighbourhoods (coordinatewise) lie in `V_ε(z^j, x, δ)` for all `x ∈ z^j + τ_j𝔹`. -/
theorem lemma_3_2_v {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hDd : Dense D) (hC1 : ContDiffOn ℝ 1 f D) (xt : EuclideanSpace ℝ (Fin n))
    (ε δ η : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hη : 0 < η) (m : ℕ) (hm : n + 1 ≤ m)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKL : K ⊆ levelSet f xt) (hKc : IsCompact K)
    (hKη : ∀ x ∈ K, η ≤ rho f D ε x) (hKne : K.Nonempty) :
    ∃ μbar > 0, ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ∃ (τ' : Fin ℓ → ℝ) (z : Fin ℓ → EuclideanSpace ℝ (Fin n))
      (zz : Fin ℓ → Fin m → EuclideanSpace ℝ (Fin n)),
      (∀ j, 0 < τ' j ∧ τ' j < ε / 3) ∧ (∀ j, z j ∈ K) ∧
      K ⊆ ⋃ j, Metric.ball (z j) (τ' j) ∧
      ∀ j, zz j ∈ Vset f D ε m (z j) (z j) δ ∧
        ∀ x ∈ Metric.closedBall (z j) (τ' j), ∀ y : Fin m → EuclideanSpace ℝ (Fin n),
          (∀ i, ‖y i - zz j i‖ ≤ μbar) → y ∈ Vset f D ε m (z j) x δ := by sorry

end GradSampling.Conv
