-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul
-- name    : LanglandsTunnell.CubicInduction.radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/02283a2f-2a51-53cb-bfdf-9589897b15e7
-- title:
--   Transport of radical Fourier coefficients along GL₂(ℚ)
-- statement:
--   Let $\psi$ be an additive character of the adele ring $\mathbb{A}_{\mathbb{Q}}$ of $\mathbb{Q}$ with values in $\mathbb{C}$ which is global, i.e. trivial on the image of $\mathbb{Q}$ under the structure map $\mathbb{Q} \to \mathbb{A}_{\mathbb{Q}}$, continuous, and not identically $1$. Let $\Phi : \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ be continuous and left invariant under the rational points, in the sense that $\Phi(\iota(\delta) h) = \Phi(h)$ for every $\delta \in \mathrm{GL}_3(\mathbb{Q})$, where $\iota$ is the entrywise map induced by $\mathbb{Q} \to \mathbb{A}_{\mathbb{Q}}$, and every $h$. Let $\gamma \in \mathrm{GL}_2(\mathbb{Q})$ and let $v : \mathrm{Fin}\,2 \to \mathbb{Q}$ satisfy $(0,1)\gamma = v$, i.e. $v$ is the second row of $\gamma$. Then for every $g \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$,
--   $$\int\!\!\int \Phi(r(z,y)\,g)\,\psi\bigl(-(v_0 z + v_1 y)\bigr) = \int\!\!\int \Phi\bigl(r(z,y)\,\mathrm{diag}(\gamma,1)\,g\bigr)\,\psi(-y),$$
--   where $r(z,y)$ is the unipotent matrix with $1$ on the diagonal, $(1,3)$-entry $z$, $(2,3)$-entry $y$ and all other entries $0$; $v_0, v_1$ are sent into $\mathbb{A}_{\mathbb{Q}}$ by the structure map; $\mathrm{diag}(\gamma,1)$ is the image of $\gamma$ in $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ under the rational-points map followed by the block embedding $M \mapsto \left(\begin{smallmatrix} M & 0 \\ 0 & 1\end{smallmatrix}\right)$; and both iterated integrals in $z$ and $y$ are taken with respect to the additive Haar measure on $\mathbb{A}_{\mathbb{Q}}$ (for its Borel structure) conditioned on the adelic box, i.e. the set of adeles whose archimedean part lies in the fundamental domain of the lattice basis of the mixed space and whose finite part is integral at every finite place.
--
--   This is the transport step in the Fourier expansion of a left $\mathrm{GL}_3(\mathbb{Q})$-invariant function along the unipotent radical of the $(2,1)$ parabolic: the coefficient attached to a rational row vector $v$ in the orbit of $(0,1)$ under the $\mathrm{GL}_2$ Levi is identified with the coefficient at $(0,1)$ of the function translated by the corresponding rational Levi element. It feeds the analysis of the slab integrals and of the nonvanishing of Whittaker coefficients used in the cubic induction for the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.radicalCoefficient_eq_radicalCoefficient_psi_neg_iotaGL_globalPoints_mul
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hcont : Continuous Φ)
    (_hinv : ∀ (δ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
      Φ (globalPointsGL 3 (𝓞 ℚ) ℚ δ * h) = Φ h)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (v : Fin 2 → ℚ)
    (_hv : Matrix.vecMul ![0, 1] (γ : Matrix (Fin 2) (Fin 2) ℚ) = v)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
        Φ (radicalP21 ![z, y] * g) *
          ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 0) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v 1) * y))
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) =
    ∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
        Φ (radicalP21 ![z, y] * (iotaGL (globalPointsGL 2 (𝓞 ℚ) ℚ γ) * g)) * ψ (-y)
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)) := by sorry
