-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_nhds_one_forall_norm_smoothingOperator_sub_le_of_setIntegral_compl_le
-- name    : LanglandsTunnell.CubicInduction.SlabL2.exists_nhds_one_forall_norm_smoothingOperator_sub_le_of_setIntegral_compl_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/7bcabbe0-e37a-5668-9d5b-f1be258ccb30
-- title:
--   Mass-concentration approximate identity for right smoothing on GL₃(A_ℚ)
-- statement:
--   Work on the group $G = \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, i.e. `AdelicGL 3 (𝓞 ℚ) ℚ`, the general linear group of $3\times 3$ matrices over the adele ring of $\mathbb{Q}$, equipped with its Borel $\sigma$-algebra [`NumberField.AdelicHaar.glBorel`](def/NumberField_AdelicHaar.html#L176) and the Haar measure [`NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ`](def/NumberField_AdelicHaar.html#L189). Given a continuous function $F : G \to \mathbb{C}$, two compact subsets $K, C \subseteq G$, and a real $\varepsilon > 0$, the assertion is that there exist a neighbourhood $U$ of the identity $1 \in G$ and a real $\delta > 0$ with the following property: for every $\varphi : G \to \mathbb{C}$ such that $\varphi(g)$ has vanishing imaginary part and non-negative real part for all $g$, such that the topological support of $\varphi$ is contained in $C$, such that $\varphi$ is integrable for the Haar measure with $\int_G \varphi \, dg = 1$, and such that the mass outside $U$ is small in the sense $\int_{U^{c}} \mathrm{Re}\,\varphi(g)\, dg \le \delta$, one has $\|(\,\varphi \ast F)(x) - F(x)\| \le \varepsilon$ for every $x \in K$, where $(\varphi \ast F)(x) = \mathrm{smoothingOperator}\ \varphi\ F\ x = \int_G \varphi(g) F(xg)\, dg$. Note that $U$ and $\delta$ are chosen uniformly in $\varphi$, subject only to the listed constraints.
--
--   This is the approximate-identity property of right convolution smoothing on $\mathrm{GL}_3$ over the adeles of $\mathbb{Q}$, in the form where the kernel $\varphi$ need not have small support but only small mass outside a small neighbourhood of $1$, its support remaining inside a fixed compact set; this is the shape available for kernels built from left $O(3)$-finite functions, which cannot be supported near the identity. It is used in the cubic-induction construction of smoothing elements, in the clause recovering the value of a form from its smoothed translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_nhds_one_forall_norm_smoothingOperator_sub_le_of_setIntegral_compl_le.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem LanglandsTunnell.CubicInduction.SlabL2.exists_nhds_one_forall_norm_smoothingOperator_sub_le_of_setIntegral_compl_le
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : Continuous F) (K C : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hK : IsCompact K) (hC : IsCompact C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U ∈ nhds (1 : AdelicGL 3 (𝓞 ℚ) ℚ), ∃ δ : ℝ, 0 < δ ∧ ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
      (∀ g, 0 ≤ (φ g).re ∧ (φ g).im = 0) → tsupport φ ⊆ C →
      Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) →
      ∫ g, φ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) = 1 →
      ∫ g in Uᶜ, (φ g).re ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤ δ →
        ∀ x ∈ K, ‖smoothingOperator φ F x - F x‖ ≤ ε := by sorry
