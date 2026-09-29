-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_ideleNorm_det_centralScalarGL_mul
-- name    : LanglandsTunnell.CubicInduction.AdelicEpstein.ideleNorm_det_centralScalarGL_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/c852191e-0b92-5190-9f8c-732f7e339494
-- title:
--   Idele norm of det(zI₃ g) is ‖z‖³‖det g‖
-- statement:
--   Let $z$ be a unit of the adele ring $\mathbb{A}_{\mathbb{Q}}$ of $\mathbb{Q}$ (formed with the ring of integers $\mathbb{Z}$ of $\mathbb{Q}$), and let $g$ be an element of `AdelicGL 3 (𝓞 ℚ) ℚ`, that is of the general linear group $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ of matrices indexed by `Fin 3`. Write $\|x\|$ for [`NumberField.TateGlobal.ideleNorm ℚ x`](def/NumberField_TateGlobalZeta.html#L19), the real number obtained from the scaling factor by which the unit $x$ distorts an additive Haar measure on $\mathbb{A}_{\mathbb{Q}}$ (the value of `distribHaarChar` at $x$, viewed in $\mathbb{R}$ through $\mathbb{R}_{\geq 0}$). Write $z\cdot I_3$ for the image `centralScalarGL 3 (𝓞 ℚ) ℚ z` of $z$ under the scalar-matrix homomorphism $\mathbb{A}_{\mathbb{Q}}^{\times}\to\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$. The assertion is the equality of real numbers
--   $$\bigl\|\det\bigl((z\cdot I_3)\,g\bigr)\bigr\| = \|z\|^{3}\cdot\bigl\|\det g\bigr\|,$$
--   where $\det$ denotes the determinant homomorphism from $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ to $\mathbb{A}_{\mathbb{Q}}^{\times}$.
--
--   This records the homogeneity of degree $3$ of the idele-norm character $g\mapsto\|\det g\|$ on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ under translation by the centre. It is used in the construction of a fundamental domain for the mirabolic subgroup and the attendant rescaling of integrals over $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, in [`LanglandsTunnell.CubicInduction.exists_isFundamentalDomain_mirabolic_and_lintegral_domainMeasure_eq_mul_lintegral`](thm.html#LanglandsTunnell.CubicInduction.exists_isFundamentalDomain_mirabolic_and_lintegral_domainMeasure_eq_mul_lintegral).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_ideleNorm_det_centralScalarGL_mul.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.AdelicEpstein.ideleNorm_det_centralScalarGL_mul
    (z : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) (g : AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ) :
    NumberField.TateGlobal.ideleNorm ℚ
        (Matrix.GeneralLinearGroup.det (centralScalarGL 3 (NumberField.RingOfIntegers ℚ) ℚ z * g))
      = NumberField.TateGlobal.ideleNorm ℚ z ^ 3
          * NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := by sorry
