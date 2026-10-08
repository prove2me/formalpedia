-- Prove2me | Theorems.Thm_KallenbergLP_OptTransient_stationary_lp_correspondence
-- name    : KallenbergLP.OptTransient.stationary_lp_correspondence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:53:51.240458+00:00
-- url     : https://prove2.me/theorems/21790590-4033-4ae5-81fd-f00f3d29e3d2
-- title:
--   Theorem 3.3.3 — transient stationary policies and feasible LP points
-- statement:
--   Assume, as throughout Section 3.3, that a transient policy exists. Fix strictly positive state weights $\beta$. The occupation map $\pi\mapsto x(\pi)$ from (3.3.11) is a bijection between transient stationary decision rules and feasible solutions of the equality-constrained linear program (3.3.7). Its inverse is $x\mapsto\pi(x)$ from (3.3.8). Moreover, an occupation point is extreme in the feasible polyhedron exactly when its stationary rule is pure:
--
--   $$
--   x(\pi)\in\operatorname{ext}(P)\quad\Longleftrightarrow\quad\pi\text{ is pure}.
--   $$
--
--   The result identifies the LP geometry that makes pure stationary policies available.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 54, Theorem 3.3.3; https://ir.cwi.nl/pub/13008

import Mathlib
import Definitions.Def_KallenbergLP_OptTransient_LinearProgram

namespace KallenbergLP.OptTransient

/-- Theorem 3.3.3, printed p. 54: the stationary occupation map and its inverse. -/
theorem stationary_lp_correspondence {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ)
    (hex : ∃ R : Policy n α, IsPolicy m R ∧ IsTransient m R)
    (hβ : ∀ i, 0 < β i) :
    (∀ π : StationaryRule n α,
      IsStationaryRule m π → IsTransient m (stationaryPolicy π) →
      IsFeasible m β (stationaryOccupation m β π)) ∧
    (∀ x : StateAction m → ℝ, IsFeasible m β x →
      IsStationaryRule m (ruleOfOccupation m x) ∧
      IsTransient m (stationaryPolicy (ruleOfOccupation m x)) ∧
      stationaryOccupation m β (ruleOfOccupation m x) = x) ∧
    (∀ π : StationaryRule n α,
      IsStationaryRule m π → IsTransient m (stationaryPolicy π) →
      ruleOfOccupation m (stationaryOccupation m β π) = π) ∧
    (∀ π : StationaryRule n α,
      IsStationaryRule m π → IsTransient m (stationaryPolicy π) →
      (stationaryOccupation m β π ∈ (feasibleSet m β).extremePoints ℝ ↔
       IsPureRule m π)) := by sorry

end KallenbergLP.OptTransient
