-- Prove2me | Theorems.Thm_LanglandsTunnell_eq_of_im_sub_eq_zero_of_re_sub_ne_zero_of_isIsotypicCuspFormAt_of_mellin_eq_archFactor_principal_of_minimalWeight
-- name    : LanglandsTunnell.eq_of_im_sub_eq_zero_of_re_sub_ne_zero_of_isIsotypicCuspFormAt_of_mellin_eq_archFactor_principal_of_minimalWeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/6a358d0a-125f-5463-8e38-c2e0b019db82
-- title:
--   Mixed parity excluded for real non-zero u₁-u₂ in minimal weight
-- statement:
--   Fix a character $\xi$ of the subgroup $Z$ attached to the carrier pins `productionPinsGeneral ℚ`, a non-zero ideal $N$ of $\mathcal O_{\mathbb Q}$, a finite set $S$ of finite places, and a Hecke eigensystem $\Theta$ over $\mathbb Q$ with complex coefficients. Let $\varphi$ on $\mathrm{GL}_2$ of the adeles of $\mathbb Q$ be non-zero and satisfy `IsIsotypicCuspFormAt`: it is a smooth cuspidal automorphic function with central character $\xi$, continuous, right invariant under the level subgroup $U(N)$, a Hecke coset eigenfunction with eigenvalue $\Theta.a\,v$ for every $v\notin S$, and transforms under the central scalar of $\det$ of the $v$-th generator by $(\mathrm{cNorm}\,v)^{-1}\Theta.b\,v$ for $v\notin S$. Assume $\varphi$ is reproduced by right convolution against some factorizable test function (a smooth compactly supported archimedean factor times a locally constant compactly supported finite factor), has weight $k_0\in\mathbb Z$ at the real place of $\mathbb Q$ in the sense of `HasArchCharacterAt₀` for the character `archWeightCharAt` of exponent $k_0$, and that its first $\psi_{\mathbb Q}$-Whittaker coefficient factorises as $W_A(\mathrm{ratArchGL2}\,g)\,W_f(\mathrm{finFactor}\,g)$ with $W_A(\mathrm{diag}(t,1))=W_r(t)$ for $t\in\mathbb R^\times$, and is not identically zero. Let $u_1,u_2\in\mathbb C$, $a_1,a_2,\mathrm{par}_0\in\mathbb Z/2$, and write $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$. Assume: $\xi$, viewed as a character of the full idele unit group, has archimedean component $x\mapsto\|x\|^{\mathrm{mult}\cdot(u_1+u_2+1)}(x/\|x\|)^{a}$ with $a$ the representative in $\{0,1\}$ of $a_1+a_2$; the minimal-weight relation $k_0=\delta(a_1+\mathrm{par}_0)+\delta(a_2+\mathrm{par}_0)$, where $\delta(0)=0$, $\delta(1)=1$; $\mathrm{par}_0=a_1$; and, for each $b\in\mathbb Z/2$ equal to $\mathrm{par}_0$ or to $\mathrm{par}_0+a_1+a_2$, that in some right half-plane the Mellin transform of $t\mapsto(W_r(t)+(-1)^{b}W_r(-t))/t$ converges and equals the archimedean factor $\Gamma_{\mathbb R}(s+u_1+\delta(a_1+b))\Gamma_{\mathbb R}(s+u_2+\delta(a_2+b))$ of the twisted parameter. Assume further that $\varphi$ is archimedean-smooth at the real place and is an eigenfunction of the archimedean Casimir operator with real eigenvalue $\mathrm{lam}$. If $u_1-u_2$ is real and non-zero, then $a_1=a_2$.
--
--   This is the mixed-parity exclusion at the real place in the archimedean analysis of the principal-series parameter attached to a cuspidal eigenform on $\mathrm{GL}_2/\mathbb Q$: unequal signs $a_1\neq a_2$ would force the minimal weight $k_0=1$, which is incompatible with a real non-zero difference $u_1-u_2$ in the presence of the Casimir eigenvalue bound. It feeds the archimedean unitarity step [`LanglandsTunnell.re_sub_eq_zero_or_im_sub_eq_zero_of_isIsotypicCuspFormAt_of_mellin_eq_archFactor_principal_of_minimalWeight`](thm.html#LanglandsTunnell.re_sub_eq_zero_or_im_sub_eq_zero_of_isIsotypicCuspFormAt_of_mellin_eq_archFactor_principal_of_minimalWeight), which supplies the local archimedean data for the converse theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_eq_of_im_sub_eq_zero_of_re_sub_ne_zero_of_isIsotypicCuspFormAt_of_mellin_eq_archFactor_principal_of_minimalWeight.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates
open AutomorphicForm
open AutomorphicForm.SiegelCovering
open LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker AutomorphicForm.CuspidalConstituent
open LanglandsTunnell

open RealArchParam in

theorem LanglandsTunnell.eq_of_im_sub_eq_zero_of_re_sub_ne_zero_of_isIsotypicCuspFormAt_of_mellin_eq_archFactor_principal_of_minimalWeight
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Θ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Θ φ)
    (hne0 : φ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (k₀ : ℤ) (hk : HasArchCharacterAt₀ ℚ (default : InfinitePlace ℚ)
      (archWeightCharAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) k₀) φ)
    (WA : GL (Fin 2) ℝ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ) (Wr : ℝ → ℂ)
    (hW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g = WA (ratArchGL2 g) * Wf (finFactor g))
    (hdiag : ∀ t : ℝˣ, WA (diagOne t) = Wr (t : ℝ))
    (hne : ∃ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g ≠ 0)
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (par₀ : ZMod 2)
    (hcen : LanglandsTunnell.Converse.IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) (default : InfinitePlace ℚ)
      ((RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent + 1)
      (((RealArchParam.principal u₁ a₁ u₂ a₂).centralSign.val : ℕ) : ℤ))
    (hk₀ : (k₀ : ℂ) = signShift (a₁ + par₀) + signShift (a₂ + par₀)) (hpar : par₀ = a₁)
    (hMel : ∀ b : ZMod 2, (b = par₀ ∨ b = par₀ + (RealArchParam.principal u₁ a₁ u₂ a₂).centralSign) →
      ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
        MellinConvergent (fun t : ℝ => (Wr t + (-1 : ℂ) ^ b.val * Wr (-t)) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (Wr t + (-1 : ℂ) ^ b.val * Wr (-t)) / (t : ℂ)) s =
            ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).archFactor s)
    (lam : ℝ) (hsm : IsArchSmoothAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ)
    (hΩ : archCasimirAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ = (lam : ℂ) • φ)
    (him : (u₁ - u₂).im = 0) (hre : (u₁ - u₂).re ≠ 0) :
    a₁ = a₂ := by sorry
