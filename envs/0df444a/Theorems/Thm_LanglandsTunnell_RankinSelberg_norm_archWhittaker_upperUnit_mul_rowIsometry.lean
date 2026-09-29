-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_norm_archWhittaker_upperUnit_mul_rowIsometry
-- name    : LanglandsTunnell.RankinSelberg.norm_archWhittaker_upperUnit_mul_rowIsometry
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/42d9822d-e2c0-5e31-b169-1784b787914b
-- title:
--   Modulus of a real Whittaker function on torus times O(2)
-- statement:
--   Fix an archimedean parameter $P$ of real type, i.e. either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb{C}$ and $a_i\in\mathbb{Z}/2$, or $\mathrm{discrete}(u,k)$ with $1\le k$; its central exponent is $u_1+u_2$, resp. $2u$, and its central sign is $a_1+a_2$, resp. $k+1$ in $\mathbb{Z}/2$. Let $kw$ assign an integer to each parity in $\mathbb{Z}/2$ and each infinite place of $\mathbb{Q}$, let $Wr$ assign to each such pair a function $\mathbb{C}\to\mathbb{C}$, and let $WA$ assign to each parity a function on $\mathrm{GL}_2(\mathbb{R})$. Assume: (`hWAZ`) for every parity, every $z\in\mathbb{R}^\times$ and every $h$, $WA(zI\cdot h)=|z|^{c+1}(z/|z|)^{\,\overline{s}}\,WA(h)$, where $c$ is the central exponent of $P$, $\overline{s}$ is the natural-number representative of its central sign, and the powers are complex; (`hWAK`) for every parity, every $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ` and every $h$, $WA(h\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(kw(\mathrm{par})(\mathrm{default}))(\kappa)\cdot WA(h)$, a unit scalar attached to $\kappa$; (`hWAt`) for every parity and every $t\in\mathbb{R}^\times$, $WA(\mathrm{diag}(t,1))=Wr(\mathrm{par})(\mathrm{default})(t)$. Then for every parity, all nonzero reals $t_1,t_2$, and every $k\in\mathrm{GL}_2(\mathbb{R})$ with $|\det k|=1$ and $\|xk_{00}+yk_{10}\|^2+\|xk_{01}+yk_{11}\|^2=\|x\|^2+\|y\|^2$ for all $x,y\in\mathbb{R}$, one has $\bigl\|WA(\mathrm{diag}(t_1,t_2)\,k)\bigr\|=|t_2|^{\,\operatorname{Re}(c)+1}\,\bigl\|Wr(\mathrm{par})(\mathrm{default})(\det k\cdot t_1/t_2)\bigr\|$, the exponent being a real power of $|t_2|$.
--
--   This is the standard modulus computation for an archimedean Whittaker function on $\mathrm{GL}_2(\mathbb{R})$ evaluated in Iwasawa coordinates: on the diagonal torus times the full orthogonal group the absolute value is determined by the central exponent and the torus profile $Wr$, with the sign of $\det k$ reflected in the argument. It is used in the majorant bookkeeping for the archimedean Rankin–Selberg integrand, being cited by [`LanglandsTunnell.RankinSelberg.exists_forall_integrable_archWhittaker_torusPair_rpow_det`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_integrable_archWhittaker_torusPair_rpow_det).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_norm_archWhittaker_upperUnit_mul_rowIsometry.lean

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

open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates in

theorem LanglandsTunnell.RankinSelberg.norm_archWhittaker_upperUnit_mul_rowIsometry
    (P : RealArchParam)
    (kw : ZMod 2 → InfinitePlace ℚ → ℤ)
    (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
    (WA : ZMod 2 → GL (Fin 2) ℝ → ℂ)
    (hWAZ : ∀ par : ZMod 2, ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ),
        WA par (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h)
          = ((((|(z : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
              (((z : ℝ) : ℂ) / ((|(z : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) * WA par h)
    (hWAK : ∀ par : ZMod 2, ∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
        WA par (h * κ) = (archWeightCharℝ (kw par default) ⟨κ, hκ⟩ : ℂ) * WA par h)
    (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
    (par : ZMod 2) (t₁ t₂ : ℝ) (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0)
    (k : GL (Fin 2) ℝ) (hk : k ∈ rowIsometrySubgroup ℝ) :
    ‖WA par (upperUnit t₁ 0 t₂ h₁ h₂ * k)‖ =
      |t₂| ^ (P.centralExponent.re + 1) *
        ‖Wr par default ((Matrix.GeneralLinearGroup.det k : ℝ) * t₁ / t₂)‖ := by sorry
