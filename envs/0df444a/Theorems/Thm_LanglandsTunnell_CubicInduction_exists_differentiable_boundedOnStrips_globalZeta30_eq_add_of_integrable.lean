-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_differentiable_boundedOnStrips_globalZeta30_eq_add_of_integrable
-- name    : LanglandsTunnell.CubicInduction.exists_differentiable_boundedOnStrips_globalZeta30_eq_add_of_integrable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/a088d8d7-45dd-5c54-a7d4-2c0d4903444a
-- title:
--   Entire norm-≥ 1 part of a GL₃× GL₁ zeta integral
-- statement:
--   Let $W$ be a complex-valued function on $GL_3$ of the adele ring of $\mathbb{Q}$ which is continuous and gauge-majorised in the sense of `IsGaugeMajorised3`: there are $t \in \mathbb{N}$, a finite set $T$ of finite places and $B \in \mathbb{R}$ such that for every $N$ there is $C$ with $W(g)=0$ whenever $g$ fails the condition `InRootLevel` for $T$ and $B$, and $\|W(g)\| \le C/\bigl(\mathrm{rootSizeProd}(g)^{t}(1+\mathrm{archRootSum}(g))^{N}\bigr)$ otherwise. Let $\chi$ be a homomorphism from the idele group $(\mathbb{A}_\mathbb{Q})^{\times}$ to $\mathbb{C}^{\times}$ that is an admissible twist, i.e. trivial on the image of $\mathbb{Q}^{\times}$, continuous and of absolute value $1$ everywhere, and let $g \in GL_3(\mathbb{A}_\mathbb{Q})$. Then there exists $E : \mathbb{C} \to \mathbb{C}$ which is entire and bounded on every vertical strip (for all $a \le b$ there is $C$ bounding $\|E(s)\|$ on $a \le \operatorname{Re} s \le b$), such that for every $s$ the value $E(s)$ is the integral, against the Haar measure on the ideles, of $W(\iota(\mathrm{diag}(a,1))\,g)\,\chi(a)\,\|a\|^{s-1}$ over the ideles $a$ with idele norm $\|a\| \ge 1$, where $\iota$ is the embedding $GL_2 \hookrightarrow GL_3$ of `iotaGL` and $\|\cdot\|$ is the module given by `TateGlobal.ideleNorm`; and there is $\sigma_1 \in \mathbb{R}$ such that for all $s$ with $\operatorname{Re} s > \sigma_1$ the full zeta integral `globalZeta30 W χ s g` over the whole idele group equals $E(s)$ plus the integral of the same integrand over the ideles of norm $< 1$.
--
--   This is the standard splitting of a $GL_3 \times GL_1$ Rankin–Selberg zeta integral into its norm-$\ge 1$ and norm-$<1$ parts, the first of which converges for all $s$ and defines an entire function bounded on vertical strips, as in the analytic input to converse theorems. It feeds the construction of the entire continuation and functional equation of `globalZeta30` in [`LanglandsTunnell.CubicInduction.exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn`](thm.html#LanglandsTunnell.CubicInduction.exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_differentiable_boundedOnStrips_globalZeta30_eq_add_of_integrable.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.Converse

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in

theorem LanglandsTunnell.CubicInduction.exists_differentiable_boundedOnStrips_globalZeta30_eq_add_of_integrable
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hWc : Continuous W) (hW : IsGaugeMajorised3 ℚ W)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχadm : IsAdmissibleTwist ℚ χ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ LanglandsTunnell.LDatum.BoundedOnStrips E ∧
      (∀ s : ℂ, E s =
        ∫ a in {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ | 1 ≤ TateGlobal.ideleNorm ℚ a},
          W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
            ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
          ∂(NumberField.Idele.idelicHaar ℚ)) ∧
      ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
        globalZeta30 W χ s g =
          E s +
            ∫ a in {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ | TateGlobal.ideleNorm ℚ a < 1},
              W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
                ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
              ∂(NumberField.Idele.idelicHaar ℚ) := by sorry
