-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_torusSheets_whittakerODE_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_of_whittaker_factorisation_rat
-- name    : LanglandsTunnell.exists_torusSheets_whittakerODE_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_of_whittaker_factorisation_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/1db19925-28c8-5d35-bf37-e015a7208765
-- title:
--   Torus sheets of a factorised Whittaker function over ℚ
-- statement:
--   Fix a character $\xi$ of the centre subgroup $Z$ of the general production pins over $\mathbb{Q}$, an ideal $N\subseteq\mathcal{O}_{\mathbb{Q}}$, a finite set $S$ of finite places, and a Hecke eigensystem $\Theta$ over $\mathbb{Q}$ with complex coefficients. Let $\varphi:\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ satisfy `IsIsotypicCuspFormAt` for these data: $\varphi$ is a smooth cuspidal automorphic function at the pins with central character $\xi$, continuous, right invariant under the level subgroup $U(N)$, a Hecke eigenfunction with eigenvalue $\Theta.a\,v$ for the coset system at each $v\notin S$, and satisfies $\varphi(\mathrm{diag}(\det g_v)\,g)=(\mathrm{cNorm}\,v)^{-1}\Theta.b\,v\cdot\varphi(g)$ for $v\notin S$. Assume $\varphi\neq0$; that $\varphi$ is reproduced by right convolution $\int\varphi(gx)\alpha(x)\,dx=\varphi(g)$ against some test function $\alpha$ factorising into a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor; that at every real place $w$ the predicate `HasArchCharacterAt₀` holds for $\varphi$ and the $n$-th power `archWeightCharAt` of the basic weight-one character, for some $n\in\mathbb{Z}$; that the $\psi_{\mathbb{Q}}$-Whittaker coefficient $g\mapsto\int\varphi(u(x)g)\psi_{\mathbb{Q}}(-x)\,d\nu(x)$ at $\alpha=1$ factorises as $W_A(g_\infty)\,W_f(g_f)$, where $g_\infty=$ `ratArchGL2` $g$ is the real component and $g_f=$ `finFactor` $g$ its finite part, with $W_A(\mathrm{diag}(t,1))=W_r(t)$ for $t\in\mathbb{R}^{\times}$, and that this Whittaker coefficient is nonzero at some $g$. Assume further, for $u_c\in\mathbb{C}$ and $a_c\in\mathbb{Z}$, that the archimedean local component of $\xi$, read as a character of the full idele unit group, is $x\mapsto\|x\|^{\,m u_c}(x/\|x\|)^{a_c}$ at the default infinite place ($m$ its multiplicity), that $\varphi$ is `IsArchSmoothAt` that real place, and that $\mathrm{archCasimirAt}\,\varphi=(\tfrac14-\nu^2)\varphi$ for some $\nu\in\mathbb{C}$. Then there exist $n\in\mathbb{Z}$, $c\in\mathbb{C}^{\times}$ and $P,Q:\mathbb{R}\to\mathbb{C}$ such that for all $y>0$ one has $W_r(y)=c\,(\sqrt y)^{u_c}P(y)$ and $W_r(-y)=c\,(\sqrt y)^{u_c}Q(y)$, with $P$ and $P'$ differentiable on $(0,\infty)$ and $y^2P''(y)+(\tfrac14-\nu^2+2\pi n y-4\pi^2y^2)P(y)=0$ there, and likewise $Q$, $Q'$ differentiable on $(0,\infty)$ with $y^2Q''(y)+(\tfrac14-\nu^2+2\pi(-n)y-4\pi^2y^2)Q(y)=0$.
--
--   This is the archimedean Whittaker differential equation for a cuspidal Casimir eigenform on $\mathrm{GL}_2$ over $\mathbb{Q}$, presented on the two connected sheets $y>0$ and $y<0$ of the split torus after stripping the central exponent $(\sqrt y)^{u_c}$; the weights $\pm n$ on the two sheets record the $\mathrm{SO}(2)$-type. It feeds the Mellin-transform step that identifies the spectral parameter $\nu$ in the archimedean unitarity argument, through [`LanglandsTunnell.ofReal_eq_laplaceEigenvalue_principal_of_archCasimirAt_eq_smul_of_mellin_eq_archFactor_principal`](thm.html#LanglandsTunnell.ofReal_eq_laplaceEigenvalue_principal_of_archCasimirAt_eq_smul_of_mellin_eq_archFactor_principal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_torusSheets_whittakerODE_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_of_whittaker_factorisation_rat.lean

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
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker AutomorphicForm.CuspidalConstituent
open LanglandsTunnell

theorem LanglandsTunnell.exists_torusSheets_whittakerODE_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_of_whittaker_factorisation_rat
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Θ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Θ φ)
    (hne0 : φ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ n : ℤ, HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ)
    (WA : GL (Fin 2) ℝ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ) (Wr : ℝ → ℂ)
    (hW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g = WA (ratArchGL2 g) * Wf (finFactor g))
    (hdiag : ∀ t : ℝˣ, WA (diagOne t) = Wr (t : ℝ))
    (hne : ∃ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g ≠ 0)
    (uc : ℂ) (ac : ℤ)
    (hcen : LanglandsTunnell.Converse.IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom)
      (default : InfinitePlace ℚ) uc ac)
    (hsm : IsArchSmoothAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ) (ν : ℂ)
    (hΩ : archCasimirAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ = (1 / 4 - ν ^ 2) • φ) :
    ∃ (n : ℤ) (c : ℂ) (P Q : ℝ → ℂ), c ≠ 0 ∧
      (∀ y : ℝ, 0 < y → Wr y = c * ((Real.sqrt y : ℝ) : ℂ) ^ uc * P y) ∧
      (∀ y : ℝ, 0 < y → Wr (-y) = c * ((Real.sqrt y : ℝ) : ℂ) ^ uc * Q y) ∧
      DifferentiableOn ℝ P (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv P) (Set.Ioi 0) ∧
      (∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv P) y
          + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((n : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2)
            * P y = 0) ∧
      DifferentiableOn ℝ Q (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv Q) (Set.Ioi 0) ∧
      (∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv Q) y
          + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * (((-n : ℤ) : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2)
            * Q y = 0) := by sorry
