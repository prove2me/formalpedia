-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_lintegral_norm_torusProfile_mul_rpow_lt_top
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_lintegral_norm_torusProfile_mul_rpow_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/75dc19cc-e6c4-506d-93a9-0b6cfbd45d7b
-- title:
--   Half-plane integrability of an archimedean torus profile
-- statement:
--   Fix an archimedean parameter $P$ of type `RealArchParam`, i.e. either `principal` with data $(u_1,a_1,u_2,a_2)$ in $\mathbb{C}\times\mathbb{Z}/2\times\mathbb{C}\times\mathbb{Z}/2$ or `discrete` with data $(u,k)$, $k\ge 1$, and a family $W_r$ assigning to each parity $\varepsilon\in\mathbb{Z}/2$ and each infinite place $w$ of $\mathbb{Q}$ a function $\mathbb{C}\to\mathbb{C}$. Four hypotheses are imposed, for every parity $\varepsilon$ and every real infinite place $w$. First, if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ (equal parity signs) and $\varepsilon=a_1$, then $W_r^{\varepsilon}(-t)=(-1)^{a_1}W_r^{\varepsilon}(t)$ for all real $t$. Second, if $P=\mathrm{discrete}(u_0,n)$ with $n\ge1$, then $W_r^{\varepsilon}(t)=0$ for all $t<0$. Third, if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\varepsilon=a_1+1$, there is an abscissa $s_0$ such that for $\operatorname{Re} s>s_0$ the function $t\mapsto (W_r^{\varepsilon}(t)+(-1)^{a_1}W_r^{\varepsilon}(-t))/t$ has convergent Mellin transform at $s$, with value $\frac{2s+u_1+u_2-1}{4\pi}$ times `archFactor` of the twisted parameter `P.twist 0 a₁` at $s$ (the twist adding $0$ to the complex exponents and $a_1$ to the parity signs; `archFactor` being the product of the associated $\Gamma_{\mathbb{R}}$-factors, resp. the $\Gamma_{\mathbb{C}}$-factor in the discrete case). Fourth, for every $b\in\mathbb{Z}/2$ with $b=\varepsilon$ or $b=\varepsilon+P.\mathrm{centralSign}$ (where the central sign is $a_1+a_2$ in the principal case and $k+1$ in the discrete case), there is an abscissa beyond which $t\mapsto (W_r^{\varepsilon}(t)+(-1)^{b}W_r^{\varepsilon}(-t))/t$ has convergent Mellin transform equal to `(P.twist 0 b).archFactor s`. The conclusion, for a fixed parity $\varepsilon$: there is $s_1\in\mathbb{R}$ such that for every real $\beta>s_1$ the lower Lebesgue integral of $(\|W_r^{\varepsilon}(y)\|+\|W_r^{\varepsilon}(-y)\|)\,y^{\beta}$ over $(0,\infty)$ is finite, and both $y\mapsto W_r^{\varepsilon}(y)$ and $y\mapsto W_r^{\varepsilon}(-y)$ are almost everywhere measurable for Lebesgue measure restricted to $(0,\infty)$; here the place is the distinguished infinite place `default` of $\mathbb{Q}$.
--
--   This is the archimedean input to the Rankin–Selberg computation at the real place of $\mathbb{Q}$: from the parity, support and Mellin laws satisfied by the torus profile of a local archimedean $\mathrm{GL}_2$ parameter one extracts a half-plane of exponents $\beta$ for which the weighted $L^1$-norm on $(0,\infty)$ is finite, together with the measurability needed to integrate. It is used by [`LanglandsTunnell.RankinSelberg.exists_forall_integrable_archWhittaker_torusPair_rpow_det`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_integrable_archWhittaker_torusPair_rpow_det), which turns it into integrability of the archimedean Whittaker carriers against a power of the determinant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_lintegral_norm_torusProfile_mul_rpow_lt_top.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem LanglandsTunnell.RankinSelberg.exists_forall_lintegral_norm_torusProfile_mul_rpow_lt_top
    (P : RealArchParam)
    (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
    (hWr1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par ∨ b = par + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (par : ZMod 2) :
    ∃ s₁ : ℝ, (∀ β : ℝ, s₁ < β →
        ∫⁻ y in Set.Ioi (0 : ℝ), (‖Wr par default y‖ₑ + ‖Wr par default (-y)‖ₑ) * ENNReal.ofReal (y ^ β) < ⊤) ∧
      AEMeasurable (fun y : ℝ => Wr par default y) (volume.restrict (Set.Ioi (0 : ℝ))) ∧
      AEMeasurable (fun y : ℝ => Wr par default (-y)) (volume.restrict (Set.Ioi (0 : ℝ))) := by sorry
