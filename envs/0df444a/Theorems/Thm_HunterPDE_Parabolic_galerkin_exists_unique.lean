-- Prove2me | Theorems.Thm_HunterPDE_Parabolic_galerkin_exists_unique
-- name    : HunterPDE.Parabolic.galerkin_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:20:47.656202+00:00
-- url     : https://prove2.me/theorems/6525923f-2fbe-42ab-b05a-ddc6a3afac2c
-- title:
--   Proposition 6.5 — existence and uniqueness of the Galerkin approximate solutions
-- statement:
--   Let $\Omega \subset \mathbb{R}^n$ be bounded and open, $T > 0$, let the coefficients of $L$ satisfy Assumption 6.1, $f \in L^2(0,T;H^{-1}(\Omega))$ and $g \in L^2(\Omega)$. Let $\{w_k\}$ be an orthonormal basis of $L^2(\Omega)$ of Dirichlet eigenfunctions and $E_N = \langle w_1, \dots, w_N\rangle$. Then for every $N \in \mathbb{N}$ there exists a unique approximate solution $u_N : [0,T] \to E_N$ of
--   $$u_t + Lu = f,\quad u = 0 \text{ on } \partial\Omega,\quad u(0) = g$$
--   in the sense of Definition 6.4: $(u_{Nt}(t), v)_{L^2} + a(u_N(t), v; t) = \langle f(t), v\rangle$ for all $v \in E_N$ and a.e. $t$, and $u_N(0) = P_N g$.
--
--   This is the first step of the Galerkin existence proof: the projected problem is a linear system of ODEs with $L^\infty$ coefficients.
--
--   **Formalization Note.** Uniqueness is as an element of $L^2(0,T;E_N)$: any two approximate solutions agree for a.e. $t \in (0,T)$. The Galerkin basis is a hypothesis `IsDirichletEigenbasis Ω w eig` (0-based indices); such a basis exists for nonempty bounded open $\Omega$ with $n \ge 1$ by the elliptic theory, and the hypothesis cannot hold for $n = 0$ or $\Omega = \emptyset$, where $L^2(\Omega)$ is finite-dimensional and the book's construction does not apply either.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 184, Proposition 6.5

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_H10
import Definitions.Def_HunterPDE_Parabolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Parabolic_WeakSolution

open MeasureTheory

namespace HunterPDE.Parabolic

/-- Proposition 6.5 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 184: under Assumption 6.1
(`Ω ⊂ ℝⁿ` bounded and open, `T > 0`, coefficients as in (1)–(2), `f ∈ L²(0, T; H⁻¹(Ω))`,
`g ∈ L²(Ω)`), with `E_N` the span of the first `N` Dirichlet eigenfunctions `w_k` of
(6.15)–(6.16), for every `N ∈ ℕ` there exists a unique approximate solution `u_N : [0, T] → E_N`
of (6.8) in the sense of Definition 6.4. Uniqueness is as an element of `L²(0, T; E_N)`: two
approximate solutions agree for a.e. `t ∈ (0, T)` (and then their continuous representatives
agree on `[0, T]`). -/
theorem galerkin_exists_unique {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (P : Coeffs n)
    (hP : P.Assumption61 Ω T) (w : ℕ → H10 n Ω) (eig : ℕ → ℝ)
    (hw : IsDirichletEigenbasis Ω w eig) (f : ℝ → Hm1 n Ω) (hf : MemLp f 2 (timeMeasure T))
    (g : Lp ℝ 2 (volume.restrict Ω)) (N : ℕ) :
    ∃ uN uNt : ℝ → H10 n Ω, IsApproxSolution Ω T P w N f g uN uNt ∧
      ∀ vN vNt : ℝ → H10 n Ω, IsApproxSolution Ω T P w N f g vN vNt →
        vN =ᵐ[timeMeasure T] uN := by sorry

end HunterPDE.Parabolic
