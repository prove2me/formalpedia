-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3
-- name    : LanglandsTunnell.CubicInduction.summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/55c6dc6e-e0c2-5482-812d-c6cb543bd2dd
-- title:
--   Mirabolic series and integrals of a gauge-majorised function on GL₃
-- statement:
--   Let $W$ be a complex-valued function on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ (the general linear group of degree $3$ over the adele ring of $\mathbb{Q}$), assumed continuous and gauge-majorised in the sense of `IsGaugeMajorised3 ℚ`: there are $t \in \mathbb{N}$, a finite set $T$ of finite places of $\mathbb{Q}$ and a real $B$ such that for every $N \in \mathbb{N}$ there is a constant $C$ with, for all $g$, both $W(g) = 0$ whenever the predicate `InRootLevel ℚ T B` fails at $g$, and $\|W(g)\| \le C / \bigl(\mathrm{rootSizeProd}(g)^{t}\,(1 + \mathrm{archRootSum}(g))^{N}\bigr)$ whenever it holds. Then six assertions hold simultaneously. Writing $m_i = \iota(\gamma_i)$ for the images in $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ of representatives $\gamma_i$ of the classes of `MirabolicIndex ℚ`, the quotient of $\mathrm{GL}_2(\mathbb{Q})$ by the right relation attached to the range of [`AutomorphicForm.unipotentGL2Hom`](def/AutomorphicForm_ConstantTerm.html#L33), embedded adelically and then in the upper left corner: (1) for each $g$ the family $i \mapsto W(m_i g)$ is summable; (2) the sum $g \mapsto \sum_i' W(m_i g)$ is slowly increasing on all of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ with respect to the gauge `gauge3 ℚ`; (3) that sum is continuous; (4) `HasWhittakerHalfPlane W` holds, i.e. there is $\sigma_0$ such that for every $\sigma \ge \sigma_0$ and every fundamental domain $D$ for the image of $\mathrm{GL}_2(\mathbb{Q})$ in $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ with respect to `adelicGLHaar`, the lower integral over $D$ of $\bigl(\sum_i' \|W(\iota(\gamma_i g))\|\bigr)\cdot \mathrm{detNorm}(g)^{\sigma}$ is finite; (5) for each $g$ there is $\sigma_0$ such that for $\sigma \ge \sigma_0$ the function $x \mapsto \|W(\iota(\mathrm{diag}(x,1))\,g)\|\cdot \|x\|^{\sigma-1}$ is integrable over the ideles for the idelic Haar measure, $\|x\|$ being the module `TateGlobal.ideleNorm`; and (6) for each $g$ there is $\sigma_0$ such that for $\sigma \ge \sigma_0$ the function $(x,u) \mapsto \|W(\iota(\mathrm{diag}(x,1))\,n_{21}(u)\,g)\|\cdot\|x\|^{\sigma-1}$ is integrable over ideles $\times$ adeles for the product of the idelic Haar measure and the adelic additive Haar measure, where $n_{21}(u)$ is the lower unipotent matrix with entry $u$ in position $(2,1)$. The idele and adele groups carry their Borel measurable structures.
--
--   This is the package of analytic estimates for a gauge-majorised Whittaker-type function on $\mathrm{GL}_3$ over $\mathbb{Q}$: absolute convergence of the mirabolic series, moderate growth and continuity of its sum, finiteness of the associated integral over a fundamental domain in a right half-plane, and Tate-style integrability of the torus and torus-times-unipotent translates. It is the hypothesis-supplying step for the construction of the global zeta integrals $Z_{3,0}$ and $Z_{3,1}$ of the cubic induction, which use it to obtain holomorphic continuation, boundedness on vertical strips and the functional equation with local root numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

theorem LanglandsTunnell.CubicInduction.summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hWc : Continuous W) (_hW : IsGaugeMajorised3 ℚ W) :
    (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g)) ∧
      IsModerateGrowth3 ℚ (fun g => ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * g)) ∧
      Continuous (fun g => ∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * g)) ∧
      HasWhittakerHalfPlane W ∧
      (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ →
        MeasureTheory.Integrable (fun x : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          ‖W (iotaGL (diagUnitGL2 x) * g)‖ * (TateGlobal.ideleNorm ℚ x : ℝ) ^ (σ - 1))
          (NumberField.Idele.idelicHaar ℚ)) ∧
      (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ →
        MeasureTheory.Integrable (fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
          ‖W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g)‖ * (TateGlobal.ideleNorm ℚ p.1 : ℝ) ^ (σ - 1))
          ((NumberField.Idele.idelicHaar ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) := by sorry
