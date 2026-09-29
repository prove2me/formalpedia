-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_isCuspLift3_translateRight_norm_eq
-- name    : LanglandsTunnell.CubicInduction.SlabL2.exists_isCuspLift3_translateRight_norm_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/2e34956d-16d6-59b7-ae6e-4caf3c435a87
-- title:
--   Isometric strongly continuous lift of right translation to cuspidal L²
-- statement:
--   Let $\omega:(\mathbb{A}_{\mathbb{Q}})^{\times}\to\mathbb{C}^{\times}$ be a homomorphism of the unit group of the adele ring of $\mathbb{Q}$ (over $\mathcal{O}_{\mathbb{Q}}$) into $\mathbb{C}^{\times}$ with $\|\omega(z)\|=1$ for all $z$, let $a,b$ be real numbers, and let $\Phi_0\subseteq \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ satisfy `IsSlabDomain a b Φ₀`, i.e. $0<a<b$ and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_3(\mathbb{Q})$ under `globalPointsGL` with respect to `slabMeasure a b`, the adelic Haar measure on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ restricted to the determinant-idele-norm slab `ideleNormDetSlab a b`. The assertion is that there exists a family $U$ assigning to each $g\in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ a continuous $\mathbb{C}$-linear endomorphism $U_g$ of `cuspidalSubspace ω a b Φ₀` (the topological closure inside $L^2$ of $\Phi_0$ of the span of the $L^2$-classes of those members of `automorphicSubmodule ω a b Φ₀` that are continuous and cuspidal along $P_{21}$ and $P_{12}$ for the indicated production-pin datum) with the following four properties: each $U_g$ is a `IsCuspLift3` lift of the right translation operator $F\mapsto (x\mapsto F(xg))$, that is, for every cusp function $F$ the translate $x\mapsto F(xg)$ is again a cusp function and $U_g$ sends the $L^2$-class of $F$ to the $L^2$-class of that translate; $\|U_g x\|=\|x\|$ for all $g$ and all $x$ in the cuspidal subspace; $U_{gh}=U_g\circ U_h$ for all $g,h$; $U_1$ is the identity; and for each $x$ the map $g\mapsto U_g x$ is continuous.
--
--   This is the unitarity and strong continuity of the right regular representation of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ on the cuspidal $L^2$-space attached to a slab fundamental domain, in the form of an existence statement for the family of translation operators. It is used in the construction of smoothing operators on that space, notably by [`LanglandsTunnell.CubicInduction.SlabL2.integral_smoothingOperator_comp_archRealLift3_mul_conj_eq`](thm.html#LanglandsTunnell.CubicInduction.SlabL2.integral_smoothingOperator_comp_archRealLift3_mul_conj_eq) and [`LanglandsTunnell.CubicInduction.smoothingModule_slabForm`](thm.html#LanglandsTunnell.CubicInduction.smoothingModule_slabForm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_isCuspLift3_translateRight_norm_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SpectralOperators3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory

theorem LanglandsTunnell.CubicInduction.SlabL2.exists_isCuspLift3_translateRight_norm_eq
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀) :
    ∃ U : AdelicGL 3 (𝓞 ℚ) ℚ → (↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)),
      (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, IsCuspLift3 ω a b Φ₀ (translateRight g) (U g)) ∧
      (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : ↥(cuspidalSubspace ω a b Φ₀)), ‖U g x‖ = ‖x‖) ∧
      (∀ g h : AdelicGL 3 (𝓞 ℚ) ℚ, U (g * h) = (U g).comp (U h)) ∧
      U 1 = ContinuousLinearMap.id ℂ ↥(cuspidalSubspace ω a b Φ₀) ∧
      ∀ x : ↥(cuspidalSubspace ω a b Φ₀), Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => U g x := by sorry
