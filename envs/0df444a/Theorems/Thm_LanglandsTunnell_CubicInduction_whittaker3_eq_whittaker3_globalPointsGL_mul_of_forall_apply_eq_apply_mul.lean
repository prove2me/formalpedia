-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_eq_whittaker3_globalPointsGL_mul_of_forall_apply_eq_apply_mul
-- name    : LanglandsTunnell.CubicInduction.whittaker3_eq_whittaker3_globalPointsGL_mul_of_forall_apply_eq_apply_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/f2519f65-5f27-53bb-bde8-235b0c6d343a
-- title:
--   Character dilation equals diagonal translation for GL₃ Whittaker coefficients
-- statement:
--   Fix a set $D$ of adelic points of $\mathrm{GL}_2$ over $\mathbb{Q}$, an assignment $U$ of a subgroup of that group to each ideal of $\mathbb{Z}$, and an assignment $\mathrm{gen}$ of such an adelic point to each height-one prime of $\mathbb{Z}$; these data, together with the box $B=\mathrm{adelicBox}\,\mathbb{Q}$ (the product of the fundamental domain of the Minkowski lattice at the archimedean place with the integral finite adeles), assemble into the carrier data `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`, whose additive measure is the Borel additive Haar measure of the adele ring of $\mathbb{Q}$ conditioned on $B$. Let $\psi,\psi'$ be complex-valued additive characters of the adele ring, with $\psi$ trivial on the image of $\mathbb{Q}$, let $a\in\mathbb{Q}$, and assume $\psi'(x)=\psi(ax)$ for all adeles $x$, where $a$ is taken in the adele ring via the structure map. Let $\Phi$ be a complex-valued function on $\mathrm{GL}_3$ of the adeles, invariant under left multiplication by the image of $\mathrm{GL}_3(\mathbb{Q})$ under the map `globalPointsGL` induced by $\mathbb{Q}\to\mathbb{A}_\mathbb{Q}$, and let $t\in\mathrm{GL}_3(\mathbb{Q})$ have underlying matrix $\mathrm{diag}(a^2,a,1)$ (so $a\neq 0$). Then for every adelic point $g$ of $\mathrm{GL}_3$, the $\psi'$-Whittaker coefficient of $\Phi$ at $g$ equals the $\psi$-Whittaker coefficient of $\Phi$ at $t\,g$, where the $\psi$-Whittaker coefficient at $h$ is the iterated integral, over the conditioned measure above, of $\Phi\bigl(u(x,y,z)\,h\bigr)\psi(-(x+y))$ in $x,y,z$, with $u(x,y,z)$ the upper triangular unipotent matrix having entries $x$ in position $(1,2)$, $y$ in position $(2,3)$ and $z$ in position $(1,3)$.
--
--   This is the elementary equivariance of the $\mathrm{GL}_3$ Whittaker coefficient in the additive character: replacing $\psi$ by its dilate $\psi(a\,\cdot)$ is the same as translating the argument by the rational diagonal matrix $\mathrm{diag}(a^2,a,1)$, the computation resting on the invariance of the box-conditioned adelic Haar measure under multiplication by a nonzero rational for functions periodic under $\mathbb{Q}$. It feeds the construction of the functional equation for the Whittaker zeta integral used in the cubic-induction step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_whittaker3_eq_whittaker3_globalPointsGL_mul_of_forall_apply_eq_apply_mul.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.whittaker3_eq_whittaker3_globalPointsGL_mul_of_forall_apply_eq_apply_mul
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ ψ' : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsPrincipalInvariantAddChar ℚ ψ)
    (a : ℚ) (hψ' : ∀ x : AdeleRing (𝓞 ℚ) ℚ, ψ' x = ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * x))
    (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Φ g)
    (t : GL (Fin 3) ℚ) (ht : (t : Matrix (Fin 3) (Fin 3) ℚ) = Matrix.diagonal ![a ^ 2, a, 1])
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ' Φ g =
      whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ (globalPointsGL 3 (𝓞 ℚ) ℚ t * g) := by sorry
