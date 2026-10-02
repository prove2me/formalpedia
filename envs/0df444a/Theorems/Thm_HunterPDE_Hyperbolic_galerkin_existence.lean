-- Prove2me | Theorems.Thm_HunterPDE_Hyperbolic_galerkin_existence
-- name    : HunterPDE.Hyperbolic.galerkin_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:39:19.180309+00:00
-- url     : https://prove2.me/theorems/29bc8670-2424-4438-b913-fa549e587ae8
-- title:
--   Proposition 7.5 — existence and uniqueness of the Galerkin approximate solutions u_N ∈ C¹([0,T]; E_N)
-- statement:
--   Under Assumption 7.1, let $f \in L^2(0,T;L^2(\Omega))$, $g \in H^1_0(\Omega)$, $h \in L^2(\Omega)$, and let $E_N$ be spanned by the first $N$ Dirichlet eigenfunctions. For every $N \in \mathbb{N}$ there exists a unique approximate solution $u_N : [0,T] \to E_N$ of (7.5) (Definition 7.4), with
--   $$u_N \in C^1([0,T];E_N), \qquad u_{Ntt} \in L^2(0,T;E_N).$$
--
--   This is the first step of the Galerkin construction: projecting the equation onto $E_N$ gives an $N\times N$ linear system of second-order ODEs with coefficients bounded in time.
--
--   **Formalization Note.** $C^1$ is stated as: $u_N$ has derivative $u_{Nt}(t)$ within $[0,T]$ at every $t \in [0,T]$, and $u_{Nt}$ is continuous there (part of `IsApproxSolution`). Uniqueness: any two approximate solutions agree on $[0,T]$. $N = 0$ ($E_0 = \{0\}$) is allowed and harmless.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 214, Proposition 7.5

import Mathlib
import Definitions.Def_HunterPDE_Hyperbolic_H10
import Definitions.Def_HunterPDE_Hyperbolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Hyperbolic_WaveOperator
import Definitions.Def_HunterPDE_Hyperbolic_Galerkin

namespace HunterPDE.Hyperbolic

open MeasureTheory Set

/-- Proposition 7.5 (Hunter, p. 214). Under Assumption 7.1, with `f ∈ L²(0, T; L²(Ω))`,
`g ∈ H¹₀(Ω)`, `h ∈ L²(Ω)` and `E_N` the span of the first `N` Dirichlet eigenfunctions, for every
`N ∈ ℕ` there exists a unique approximate solution `u_N : [0, T] → E_N` of (7.5)
(Definition 7.4), and it satisfies `u_N ∈ C¹([0, T]; E_N)` (`u_N` is differentiable on `[0, T]`
with the continuous derivative `u_Nt`) and `u_Ntt ∈ L²(0, T; E_N)`. Uniqueness: any two
approximate solutions agree on `[0, T]`. -/
theorem galerkin_existence {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ)
    (P : Coeffs n) (hA : Assumption71 Ω T P)
    (w : ℕ → H10 n Ω) (lam : ℕ → ℝ) (hw : IsDirichletEigenbasis w lam)
    (f : ℝ → L2 n Ω) (hf : MemLp f 2 (volume.restrict (Ioo 0 T))) (g : H10 n Ω) (h : L2 n Ω)
    (N : ℕ) :
    (∃ uN uN_t uN_tt : ℝ → H10 n Ω, IsApproxSolution Ω T P w N f g h uN uN_t uN_tt ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt uN (uN_t t) (Icc 0 T) t)) ∧
      ∀ uN uN_t uN_tt uN' uN'_t uN'_tt : ℝ → H10 n Ω,
        IsApproxSolution Ω T P w N f g h uN uN_t uN_tt →
        IsApproxSolution Ω T P w N f g h uN' uN'_t uN'_tt →
        ∀ t ∈ Icc 0 T, uN' t = uN t := by sorry

end HunterPDE.Hyperbolic
