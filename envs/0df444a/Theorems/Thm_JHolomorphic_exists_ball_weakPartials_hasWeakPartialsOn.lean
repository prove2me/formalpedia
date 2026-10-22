-- Prove2me | Theorems.Thm_JHolomorphic_exists_ball_weakPartials_hasWeakPartialsOn
-- name    : JHolomorphic.exists_ball_weakPartials_hasWeakPartialsOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T14:15:31.843829+00:00
-- url     : https://prove2.me/theorems/98e0e73c-4f02-47d7-b9f3-c3d2039cac8c
-- title:
--   A $W^{1,p}$ solution of $\partial_s u+J(u)\,\partial_t u=0$ with $p>2$ is of class $W^{2,p}$ near every point
-- statement:
--   Let $p>2$, let $E$ be a finite-dimensional real normed space and let $J$ be a smooth almost complex structure on an open set $O\subseteq E$. Let $U\subseteq\mathbb{C}$ be open and let $u:U\to O$ be continuous with weak partial derivatives $u_s,u_t$ on $U$, such that $u,u_s,u_t\in L^p(K)$ for every compact $K\subseteq U$ and $u_s+J(u)\,u_t=0$ almost everywhere on $U$. Then for every $z_0\in U$ there is $r>0$ with $B(z_0,r)\subseteq U$ such that $u_s$ and $u_t$ have weak partial derivatives $u_{ss},u_{st}$ and $u_{ts},u_{tt}$ on $B(z_0,r)$, and all four lie in $L^p(B(z_0,r))$. In other words, $u$ is of class $W^{2,p}$ near every point of $U$.
--
--   **Formalization Note** Weak partial derivatives are `HasWeakPartialsOn`, tested against real $C^\infty$ functions with compact support in the given open set; $u_s$ is the derivative in the direction $1$ and $u_t$ in the direction $i$. The weak partials $u_s,u_t$ of $u$ are fixed in advance (hypothesis `hw`), and the conclusion is about these same functions. $L^p$ membership is `MemLp _ (ENNReal.ofReal p)` for the Lebesgue measure restricted to the set. The radius $r$ may depend on $z_0$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 2, Theorem 2.22 (1) and Exercise 2.23

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

/-- Let `p > 2` and let `J` be a smooth almost complex structure on an open set `O ⊆ E`. Let
`u : U → O` be a continuous `W^{1,p}_loc` solution of `∂ₛu + J(u) ∂ₜu = 0` on an open set
`U ⊆ ℂ`, with weak partial derivatives `uₛ`, `uₜ`. Then every point `z₀ ∈ U` is the centre of a
disc `B(z₀, r) ⊆ U` on which `uₛ` and `uₜ` have weak partial derivatives lying in
`L^p(B(z₀, r))`. -/
theorem exists_ball_weakPartials_hasWeakPartialsOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O) (U : Set ℂ) (hU : IsOpen U)
    (u us ut : ℂ → E) (hu : ContinuousOn u U) (huO : Set.MapsTo u U O)
    (hw : HasWeakPartialsOn U u us ut)
    (hLp : ∀ K ⊆ U, IsCompact K →
      MemLp u (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp us (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp ut (ENNReal.ofReal p) (volume.restrict K))
    (heq : ∀ᵐ z ∂(volume.restrict U), us z + J (u z) (ut z) = 0) :
    ∀ z₀ ∈ U, ∃ r > (0 : ℝ), ball z₀ r ⊆ U ∧ ∃ uss ust uts utt : ℂ → E,
      HasWeakPartialsOn (ball z₀ r) us uss ust ∧ HasWeakPartialsOn (ball z₀ r) ut uts utt ∧
      MemLp uss (ENNReal.ofReal p) (volume.restrict (ball z₀ r)) ∧
      MemLp ust (ENNReal.ofReal p) (volume.restrict (ball z₀ r)) ∧
      MemLp uts (ENNReal.ofReal p) (volume.restrict (ball z₀ r)) ∧
      MemLp utt (ENNReal.ofReal p) (volume.restrict (ball z₀ r)) := by
  sorry

end JHolomorphic
