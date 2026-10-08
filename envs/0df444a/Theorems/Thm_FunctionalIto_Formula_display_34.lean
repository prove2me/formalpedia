-- Prove2me | Theorems.Thm_FunctionalIto_Formula_display_34
-- name    : FunctionalIto.Formula.display_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:30.885054+00:00
-- url     : https://prove2.me/theorems/876d955e-9790-4d44-8792-e2032165453b
-- title:
--   Display (34), p. 12 — the horizontal increment is the integral of the horizontal derivative along the flat extension
-- statement:
--   Let $F\in\mathbb C^{1,2}_b([0,T))$ with horizontal derivative $\mathcal DF$. For every $t\ge0$ and $h\ge0$ with $t+h<T$ and every $(x,v)\in D([0,t],\mathbb R^d)\times\mathcal S_t$,
--   $$F_{t+h}(x_{t,h},v_{t,h})-F_t(x_t,v_t)=\int_0^h\mathcal D_{t+u}F(x_{t,u},v_{t,u})\,du,$$
--   where $x_{t,u}$ is the horizontal extension (4) of $x_t$ to $[0,t+u]$.
--
--   In the proof of Theorem 4.1 this identity handles the horizontal part of each increment of $F$ along a piecewise constant approximation of $(X,A)$.
--
--   **Formalization Note.** The paper states (34) for the step approximations ${}_nX,{}_nA$ at the random times $\tau^n_i$; its argument (the map $u\mapsto F_{t+u}(x_{t,u},v_{t,u})$ is right-differentiable and left-continuous) applies to any stopped path, and the paper's instance is a substitution. The flat extension $x_{t,u}$ is the stopped path $x_t$ viewed at horizon $t+u$.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, p. 12, proof of Theorem 4.1, display (34)

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_FunctionalIto_Formula_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace FunctionalIto.Formula

/-- Display (34) (p. 12), for an arbitrary stopped path: for `F ∈ ℂ_b^{1,2}([0,T))`, every
`(x, v) ∈ D([0,t], ℝ^d) × 𝒮_t` and `h ≥ 0` with `t + h < T`, the horizontal increment along
the flat extension equals the integral of the horizontal derivative:
`F_{t+h}(x_{t,h}, v_{t,h}) − F_t(x_t, v_t) = ∫_0^h 𝒟_{t+u}F(x_{t,u}, v_{t,u}) du`. -/
theorem display_34 {d : ℕ} (T : ℝ≥0) (F DF : Functional d ℝ) (DxF : Functional d (Fin d → ℝ))
    (DxxF : Functional d (Matrix (Fin d) (Fin d) ℝ)) (hF : IsC12b T F DF DxF DxxF)
    (t h : ℝ≥0) (hth : t + h < T) (x : Path d) (v : MPath d) (hxv : Admissible t x v) :
    F (t + h) (stop t x) (stop t v) - F t x v =
      ∫ u in (0 : ℝ)..(h : ℝ), DF (t + u.toNNReal) (stop t x) (stop t v) := by sorry

end FunctionalIto.Formula
