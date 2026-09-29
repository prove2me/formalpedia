-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_forall_apply_principalSeries2Rep_eq_det_mul_of_norm_eq_one
-- name    : LanglandsTunnell.CubicInduction.eq_zero_of_forall_apply_principalSeries2Rep_eq_det_mul_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/72d8eaa6-5d59-5b97-bf62-12c93e3c7469
-- title:
--   Vanishing of χ∘det-equivariant functionals on a principal series
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, and write $F$ for the completion of $\mathbb{Q}$ at $p$. Let $\theta_0,\theta_1 \colon F^\times \to \mathbb{C}^\times$ be group homomorphisms (indexed by $i \in \mathrm{Fin}\ 2$) whose values all have complex absolute value $1$, and suppose given levels $c_0, c_1 \in \mathbb{N}$ such that $\theta_i$ is trivial on `higherUnitsAt ℚ p (c i)`, i.e. on the set of units $u$ with $v(u) = 1$ and, unless $c_i = 0$, $v(u-1) \le \exp(-c_i)$. Let $\chi \colon F^\times \to \mathbb{C}^\times$ be a further homomorphism. Consider the $\mathbb{C}$-subspace `principalSeries2 p θ` of functions $f \colon \mathrm{GL}_2(F) \to \mathbb{C}$ that are locally constant, satisfy $f\big(\begin{pmatrix}1&x\\0&1\end{pmatrix}g\big) = f(g)$ for all $x \in F$, and satisfy $f(\mathrm{diag}(a_0,a_1)g) = \theta_0(a_0)\theta_1(a_1)\sqrt{\|a_0\|/\|a_1\|}\, f(g)$ for all $a_0,a_1 \in F^\times$; it carries the right-translation action $(\rho(g)f)(h) = f(hg)$. The assertion is: if a $\mathbb{C}$-linear functional $\lambda$ on this space satisfies $\lambda(\rho(g)f) = \chi(\det g)\,\lambda(f)$ for all $g \in \mathrm{GL}_2(F)$ and all $f$ in the space, then $\lambda = 0$.
--
--   This is the statement that $\mathrm{Hom}_{\mathrm{GL}_2(F)}\big(I(\theta_0,\theta_1), \chi \circ \det\big) = 0$ for a normalised principal series with unitary inducing characters of finite level: no one-dimensional quotient of such a principal series is given by a character of the determinant. It is used in establishing that a submodule of `principalSeries2` stable under right translation and containing enough differences $\rho(u)f - f$ for upper unipotent $u$ is the whole space, part of the local analysis of induced representations in the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eq_zero_of_forall_apply_principalSeries2Rep_eq_det_mul_of_norm_eq_one.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.eq_zero_of_forall_apply_principalSeries2Rep_eq_det_mul_of_norm_eq_one
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hθu : ∀ (i : Fin 2) (z : (p.adicCompletion ℚ)ˣ), ‖((θ i z : ℂˣ) : ℂ)‖ = 1)
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (lam : ↥(principalSeries2 p θ) →ₗ[ℂ] ℂ)
    (hlam : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)) (f : ↥(principalSeries2 p θ)),
      lam (principalSeries2Rep θ g f) = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * lam f) :
    lam = 0 := by sorry
