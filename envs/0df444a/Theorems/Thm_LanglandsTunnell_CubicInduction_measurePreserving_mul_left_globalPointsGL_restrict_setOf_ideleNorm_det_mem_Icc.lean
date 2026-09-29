-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc
-- name    : LanglandsTunnell.CubicInduction.measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/4f5e7f06-3922-5ae9-a338-d51dd63e71c1
-- title:
--   Rational left translations preserve the adelic GL₃ determinant slab
-- statement:
--   Work with $\mathbb{A} =$ the adele ring of $\mathbb{Q}$ (the adele ring of $\mathbb{Q}$ relative to its ring of integers) and with $G = \mathrm{GL}_3(\mathbb{A})$, the group `AdelicGL 3` of invertible $3\times 3$ matrices over $\mathbb{A}$, equipped with the Borel $\sigma$-algebra of its topology and with the Haar measure $\mu =$ `adelicGLHaar`. For an invertible adele $x$, the quantity `ideleNorm` $\|x\|$ is the real number obtained from the module character `distribHaarChar` of $\mathbb{A}$ evaluated at $x$. Let $a, b$ be arbitrary real numbers — no relation between them is assumed — and put $S = \{g \in G : \|\det g\| \in [a,b]\}$. Let $\gamma \in \mathrm{GL}_3(\mathbb{Q})$, and let $\gamma_{\mathbb{A}} \in G$ be its image under `globalPointsGL`, the monoid homomorphism induced entrywise by the structure map $\mathbb{Q} \to \mathbb{A}$. The assertion is that the map $g \mapsto \gamma_{\mathbb{A}} g$ is measure preserving from $\mu$ restricted to $S$ to $\mu$ restricted to $S$: it is measurable, and the pushforward of $\mu|_S$ along it equals $\mu|_S$.
--
--   This is the invariance statement underlying the use of determinant slabs $a \le \|\det g\| \le b$ as fundamental-domain truncations for $\mathrm{GL}_3(\mathbb{Q})$ acting on $\mathrm{GL}_3(\mathbb{A})$, the slab being stable under rational left translation because principal ideles have idelic norm $1$. It is used in the adelic Epstein-series and $L^2$-estimates on slabs that enter the cubic induction step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem LanglandsTunnell.CubicInduction.measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc
    (a b : ℝ) (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    MeasurePreserving
      (fun g : LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ =>
        LanglandsTunnell.CubicInduction.globalPointsGL 3 (NumberField.RingOfIntegers ℚ) ℚ γ * g)
      ((NumberField.AdelicHaar.adelicGLHaar (Fin 3) (NumberField.RingOfIntegers ℚ) ℚ).restrict
        {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b})
      ((NumberField.AdelicHaar.adelicGLHaar (Fin 3) (NumberField.RingOfIntegers ℚ) ℚ).restrict
        {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) := by sorry
