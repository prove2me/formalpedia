-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_ideleNorm_det_globalPointsGL_eq_one_and_measurableSet_ideleNormDetSlab
-- name    : LanglandsTunnell.CubicInduction.ideleNorm_det_globalPointsGL_eq_one_and_measurableSet_ideleNormDetSlab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/ab657db6-f5ed-5670-8ee9-c3cea185a43b
-- title:
--   Unimodularity of rational determinants; Borel determinant slabs
-- statement:
--   Two assertions about $\mathrm{GL}_3$ over the adeles of $\mathbb{Q}$ are combined. Write $\mathbb{A} = \mathrm{AdeleRing}\,(\mathcal{O}_{\mathbb{Q}})\,\mathbb{Q}$, let `AdelicGL 3 (𝓞 ℚ) ℚ` be $\mathrm{GL}_3(\mathbb{A})$, and for an idele $x \in \mathbb{A}^\times$ let $\mathrm{ideleNorm}\,\mathbb{Q}\,(x)$ denote the real number obtained from the value at $x$ of the distributive Haar character of the multiplicative action of $\mathbb{A}^\times$ on $\mathbb{A}$, a non-negative real scaling factor coerced to $\mathbb{R}$. First: for every $\gamma \in \mathrm{GL}_3(\mathbb{Q})$, the idele norm of the determinant of the image of $\gamma$ under `globalPointsGL 3 (𝓞 ℚ) ℚ`, the homomorphism $\mathrm{GL}_3(\mathbb{Q}) \to \mathrm{GL}_3(\mathbb{A})$ induced entrywise by the structure map $\mathbb{Q} \to \mathbb{A}$, equals $1$. Second: for all real numbers $a$ and $b$, the subset of $\mathrm{GL}_3(\mathbb{A})$ consisting of those $g$ with $\mathrm{ideleNorm}\,\mathbb{Q}\,(\det g) \in [a,b]$ is measurable for the $\sigma$-algebra [`NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ`](def/NumberField_AdelicHaar.html#L176), namely the Borel $\sigma$-algebra of the topology of $\mathrm{GL}_3(\mathbb{A})$.
--
--   The first clause is the product formula for $\mathbb{Q}$, in the form that a principal idele arising from $\det \gamma \in \mathbb{Q}^\times$ has idele norm $1$, so that left translation by $\mathrm{GL}_3(\mathbb{Q})$ preserves each determinant slab; the second records that those slabs are Borel. Both are used by the analysis of slab fundamental domains on $\mathrm{GL}_3(\mathbb{A})$, for instance in establishing finiteness of the slab measure and estimates for smoothing operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_ideleNorm_det_globalPointsGL_eq_one_and_measurableSet_ideleNormDetSlab.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.ideleNorm_det_globalPointsGL_eq_one_and_measurableSet_ideleNormDetSlab :
    (∀ γ : GL (Fin 3) ℚ,
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ)) = 1) ∧
    ∀ a b : ℝ, @MeasurableSet (AdelicGL 3 (𝓞 ℚ) ℚ) (NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ)
      {g : AdelicGL 3 (𝓞 ℚ) ℚ | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} := by sorry
