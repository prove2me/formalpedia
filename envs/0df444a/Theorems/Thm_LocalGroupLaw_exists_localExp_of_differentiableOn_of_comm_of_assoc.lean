-- Prove2me | Theorems.Thm_LocalGroupLaw_exists_localExp_of_differentiableOn_of_comm_of_assoc
-- name    : LocalGroupLaw.exists_localExp_of_differentiableOn_of_comm_of_assoc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/ea98b962-dbd6-56d5-8d80-e003533d8998
-- title:
--   Local exponential of a holomorphic commutative local group law
-- statement:
--   Fix $g \in \mathbb{N}$ and a real $\rho > 0$, and let $F : (\mathrm{Fin}\,g \to \mathbb{C}) \to (\mathrm{Fin}\,g \to \mathbb{C}) \to (\mathrm{Fin}\,g \to \mathbb{C})$ be a map of two vector variables on $\mathbb{C}^g$ such that the associated function of the pair is complex differentiable on the product $B(0,\rho) \times B(0,\rho)$ of metric balls about the origin. Assume: $F(0,v) = v$ and $F(v,0) = v$ for every $v \in B(0,\rho)$; $F(v,w) = F(w,v)$ for all $v, w \in B(0,\rho)$; and $F(F(u,v),w) = F(u,F(v,w))$ for all $u,v,w \in B(0,\rho)$ subject to the proviso that both $F(u,v)$ and $F(v,w)$ again lie in $B(0,\rho)$. The conclusion produces a radius $r > 0$ together with a map $e : \mathbb{C}^g \to \mathbb{C}^g$ such that $e(0) = 0$; $e$ is complex differentiable on $B(0,r)$; $e$ has Fréchet derivative the identity continuous linear map at $0$; $e$ is injective on $B(0,r)$; $e$ maps $B(0,r)$ into $B(0,\rho)$; $e(v+w) = F(e(v),e(w))$ whenever $v$, $w$ and $v+w$ all lie in $B(0,r)$; and there is $\delta > 0$ such that every $x \in B(0,\delta)$ is of the form $e(v)$ for some $v \in B(0,r)$.
--
--   This is the analytic core of the local exponential map of a commutative holomorphic (formal) group law: it linearises $F$ near the origin, identifying it with vector addition on a small ball, with the image of the chart containing a ball. It is stated purely in terms of balls in $\mathbb{C}^g$ and is used to construct the local exponential of a smooth commutative group scheme over $\mathbb{C}$, where $F$ is the group law read in a chart at the identity, in [`GoodReductionJacobian.RelativeGroupLaw.exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension). The upgrade of complex differentiability on an open subset of $\mathbb{C}^g$ to infinite smoothness is supplied by [`Complex.contDiffOn_infty_of_differentiableOn_pi`](thm.html#Complex.contDiffOn_infty_of_differentiableOn_pi).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGroupLaw_exists_localExp_of_differentiableOn_of_comm_of_assoc.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Topology

theorem LocalGroupLaw.exists_localExp_of_differentiableOn_of_comm_of_assoc
    {g : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (F : (Fin g → ℂ) → (Fin g → ℂ) → (Fin g → ℂ))
    (hF : DifferentiableOn ℂ (fun p : (Fin g → ℂ) × (Fin g → ℂ) => F p.1 p.2)
      (Metric.ball (0 : Fin g → ℂ) ρ ×ˢ Metric.ball (0 : Fin g → ℂ) ρ))
    (hzero_left : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) ρ, F 0 v = v)
    (hzero_right : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) ρ, F v 0 = v)
    (hcomm : ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) ρ → w ∈ Metric.ball (0 : Fin g → ℂ) ρ →
      F v w = F w v)
    (hassoc : ∀ u v w : Fin g → ℂ, u ∈ Metric.ball (0 : Fin g → ℂ) ρ → v ∈ Metric.ball (0 : Fin g → ℂ) ρ →
      w ∈ Metric.ball (0 : Fin g → ℂ) ρ → F u v ∈ Metric.ball (0 : Fin g → ℂ) ρ →
      F v w ∈ Metric.ball (0 : Fin g → ℂ) ρ → F (F u v) w = F u (F v w)) :
    ∃ (r : ℝ) (_ : 0 < r) (e : (Fin g → ℂ) → (Fin g → ℂ)),
      e 0 = 0 ∧
      DifferentiableOn ℂ e (Metric.ball (0 : Fin g → ℂ) r) ∧
      HasFDerivAt e (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 ∧
      Set.InjOn e (Metric.ball (0 : Fin g → ℂ) r) ∧
      Set.MapsTo e (Metric.ball (0 : Fin g → ℂ) r) (Metric.ball (0 : Fin g → ℂ) ρ) ∧
      (∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) r → w ∈ Metric.ball (0 : Fin g → ℂ) r →
        v + w ∈ Metric.ball (0 : Fin g → ℂ) r → e (v + w) = F (e v) (e w)) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Metric.ball (0 : Fin g → ℂ) δ,
        ∃ v ∈ Metric.ball (0 : Fin g → ℂ) r, e v = x) := by sorry
