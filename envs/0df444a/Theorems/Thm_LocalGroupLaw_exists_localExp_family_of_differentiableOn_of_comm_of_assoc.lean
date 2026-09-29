-- Prove2me | Theorems.Thm_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc
-- name    : LocalGroupLaw.exists_localExp_family_of_differentiableOn_of_comm_of_assoc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/8f58ff6d-5b15-55e1-9fad-54e93ef2f9ab
-- title:
--   Holomorphic local exponential for a family of commutative local group laws
-- statement:
--   Let $P$ and $E$ be finite-dimensional complex normed spaces, let $z_0 \in P$ and let $\sigma, \rho > 0$. Suppose $F : P \to E \to E \to E$ is such that $(z,v,w) \mapsto F\,z\,v\,w$ is $\mathbb{C}$-differentiable on $B(z_0,\sigma) \times (B(0,\rho) \times B(0,\rho))$, and that for each $z \in B(z_0,\sigma)$ the law $F_z$ has $0$ as a two-sided unit ($F_z(0,v) = v = F_z(v,0)$ for $v \in B(0,\rho)$), is commutative on $B(0,\rho)$, and is associative in the guarded sense that $F_z(F_z(u,v),w) = F_z(u,F_z(v,w))$ whenever $u,v,w \in B(0,\rho)$ and both $F_z(u,v)$ and $F_z(v,w)$ lie in $B(0,\rho)$. Then there exist radii $0 < \sigma' \le \sigma$, $r > 0$, $\delta > 0$ and maps $e, \ell : P \to E \to E$ with $(z,v) \mapsto e\,z\,v$ $\mathbb{C}$-differentiable on $B(z_0,\sigma') \times B(0,r)$ and $(z,x) \mapsto \ell\,z\,x$ $\mathbb{C}$-differentiable on $B(z_0,\sigma') \times B(0,\delta)$, such that for every $z \in B(z_0,\sigma')$: $e_z(0) = 0$; $e_z$ has Fréchet derivative the identity of $E$ at $0$; $e_z$ is injective on $B(0,r)$ and maps $B(0,r)$ into $B(0,\rho)$; $e_z(v+w) = F_z(e_z(v),e_z(w))$ whenever $v,w,v+w \in B(0,r)$; every $x \in B(0,\delta)$ is $e_z(v)$ for some $v \in B(0,r)$; $\ell_z(e_z(v)) = v$ for $v \in B(0,r)$; and for $x \in B(0,\delta)$ one has $\ell_z(x) \in B(0,r)$ and $e_z(\ell_z(x)) = x$.
--
--   This is the parametric (holomorphic-family) version of the construction of the local exponential and local logarithm of a commutative formal/local group law, with all radii chosen uniformly for parameters near $z_0$. It is used to produce a holomorphic family of local isomorphisms from the additive group in the uniformisation of the fake elliptic curves arising in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGroupLaw_exists_localExp_family_of_differentiableOn_of_comm_of_assoc.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Topology

theorem LocalGroupLaw.exists_localExp_family_of_differentiableOn_of_comm_of_assoc
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (z₀ : P) {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) (F : P → E → E → E)
    (hF : DifferentiableOn ℂ (fun q : P × (E × E) => F q.1 q.2.1 q.2.2)
      (Metric.ball z₀ σ ×ˢ (Metric.ball (0 : E) ρ ×ˢ Metric.ball (0 : E) ρ)))
    (hzero_left : ∀ z ∈ Metric.ball z₀ σ, ∀ v ∈ Metric.ball (0 : E) ρ, F z 0 v = v)
    (hzero_right : ∀ z ∈ Metric.ball z₀ σ, ∀ v ∈ Metric.ball (0 : E) ρ, F z v 0 = v)
    (hcomm : ∀ z ∈ Metric.ball z₀ σ, ∀ v w : E, v ∈ Metric.ball (0 : E) ρ → w ∈ Metric.ball (0 : E) ρ →
      F z v w = F z w v)
    (hassoc : ∀ z ∈ Metric.ball z₀ σ, ∀ u v w : E, u ∈ Metric.ball (0 : E) ρ → v ∈ Metric.ball (0 : E) ρ →
      w ∈ Metric.ball (0 : E) ρ → F z u v ∈ Metric.ball (0 : E) ρ → F z v w ∈ Metric.ball (0 : E) ρ →
      F z (F z u v) w = F z u (F z v w)) :
    ∃ (σ' r δ : ℝ) (e ℓ : P → E → E), 0 < σ' ∧ σ' ≤ σ ∧ 0 < r ∧ 0 < δ ∧
      DifferentiableOn ℂ (fun q : P × E => e q.1 q.2) (Metric.ball z₀ σ' ×ˢ Metric.ball (0 : E) r) ∧
      DifferentiableOn ℂ (fun q : P × E => ℓ q.1 q.2) (Metric.ball z₀ σ' ×ˢ Metric.ball (0 : E) δ) ∧
      ∀ z ∈ Metric.ball z₀ σ',
        e z 0 = 0 ∧
        HasFDerivAt (e z) (ContinuousLinearMap.id ℂ E) 0 ∧
        Set.InjOn (e z) (Metric.ball (0 : E) r) ∧
        Set.MapsTo (e z) (Metric.ball (0 : E) r) (Metric.ball (0 : E) ρ) ∧
        (∀ v w : E, v ∈ Metric.ball (0 : E) r → w ∈ Metric.ball (0 : E) r → v + w ∈ Metric.ball (0 : E) r →
          e z (v + w) = F z (e z v) (e z w)) ∧
        (∀ x ∈ Metric.ball (0 : E) δ, ∃ v ∈ Metric.ball (0 : E) r, e z v = x) ∧
        (∀ v ∈ Metric.ball (0 : E) r, ℓ z (e z v) = v) ∧
        (∀ x ∈ Metric.ball (0 : E) δ, ℓ z x ∈ Metric.ball (0 : E) r ∧ e z (ℓ z x) = x) := by sorry
