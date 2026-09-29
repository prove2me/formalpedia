-- Prove2me | Theorems.Thm_LanglandsTunnell_ofReal_eq_laplaceEigenvalue_principal_of_archCasimirAt_eq_smul_of_mellin_eq_archFactor_principal
-- name    : LanglandsTunnell.ofReal_eq_laplaceEigenvalue_principal_of_archCasimirAt_eq_smul_of_mellin_eq_archFactor_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/a4a42874-6d49-530f-a7a2-7c853c4a6fc0
-- title:
--   Casimir eigenvalue equals the principal-series Laplace eigenvalue
-- statement:
--   Work over $\mathbb{Q}$ with the carrier data `productionPinsGeneral ℚ`. Let $\xi$ be a character of its centre subgroup $Z$ with values in $\mathbb{C}^\times$, $N$ an ideal of $\mathbb{Z}$, $S$ a finite set of finite places, $\Theta$ a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients $a,b$, and $\varphi : \mathrm{GL}_2(\mathbb{A}_\mathbb{Q}) \to \mathbb{C}$ an isotypic cusp form for these data: $\varphi$ is a smooth cuspidal automorphic function with central character $\xi$, continuous, invariant under right translation by the level subgroup $U(N)$, a Hecke coset eigenfunction with eigenvalue $\Theta.a\,v$ at each $v \notin S$, and satisfies $\varphi(\mathrm{diag}(\det \mathrm{gen}(v))g) = (\mathrm{cNorm}\,v)^{-1}\,\Theta.b\,v \cdot \varphi(g)$ for $v \notin S$. Assume $\varphi \neq 0$; that $\varphi$ is reproduced by right convolution with some factorizable test function (smooth compactly supported archimedean factor, locally constant compactly supported finite factor); that at every real place $w$ the form transforms by `archWeightCharAt hw n` for some $n \in \mathbb{Z}$, in the sense of the predicate `HasArchCharacterAt₀`. Let $W_A$ on $\mathrm{GL}_2(\mathbb{R})$, $W_f$ on the finite adelic subgroup and $W_r$ on $\mathbb{R}$ be such that the $\psi_\mathbb{Q}$-Whittaker coefficient $\int \varphi(u(x)g)\psi_\mathbb{Q}(-x)\,d\nu(x)$ at $\alpha = 1$ equals $W_A(\mathrm{ratArchGL2}\,g)\cdot W_f(\mathrm{finFactor}\,g)$ for all $g$, that $W_A(\mathrm{diag}(t,1)) = W_r(t)$ for $t \in \mathbb{R}^\times$, and that this Whittaker coefficient is nonzero at some $g$. Let $u_1,u_2 \in \mathbb{C}$, $a_1,a_2,\mathrm{par}_0 \in \mathbb{Z}/2$ and put $P = \mathrm{principal}\,u_1\,a_1\,u_2\,a_2$. Assume the archimedean component at the unique infinite place of $\xi$, transported to the full idele unit group, is $x \mapsto \|x\|^{\mathrm{mult}\cdot(u_1+u_2+1)}(x/\|x\|)^{(a_1+a_2).\mathrm{val}}$ in the sense of `IsArchCompAt`; and that for each $b \in \mathbb{Z}/2$ with $b = \mathrm{par}_0$ or $b = \mathrm{par}_0 + (a_1+a_2)$ there is $s_0 \in \mathbb{R}$ such that for $\mathrm{Re}\,s > s_0$ the Mellin transform of $t \mapsto (W_r(t) + (-1)^{b.\mathrm{val}}W_r(-t))/t$ converges and equals the archimedean factor $\Gamma_\mathbb{R}(s+u_1+\mathrm{signShift}(a_1+b))\,\Gamma_\mathbb{R}(s+u_2+\mathrm{signShift}(a_2+b))$ of the twist of $P$ by $(0,b)$. Finally let $\lambda \in \mathbb{R}$, assume $\varphi$ is smooth at the real place (each $e \mapsto \varphi(g \cdot \mathrm{archRealLiftAt}\,e)$ is $C^\infty$ on invertible matrices), and that the archimedean Casimir operator built from the right-translation derivatives in the directions $H$, $E$, $F^-$ sends $\varphi$ to $\lambda \cdot \varphi$. Then $\lambda = 1/4 - ((u_1-u_2)/2)^2$, the Laplace eigenvalue attached to $P$.
--
--   This is the archimedean compatibility step identifying the Casimir (hyperbolic Laplace) eigenvalue of a cuspidal Whittaker vector with the parameter of the principal series dictated by the gamma factors of its Mellin data. It feeds the archimedean unitarity argument: the statement is used in deducing that $u_1-u_2$ is purely imaginary or real, and in the variant recording the existence of a real square relation for the Casimir eigenvalue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_ofReal_eq_laplaceEigenvalue_principal_of_archCasimirAt_eq_smul_of_mellin_eq_archFactor_principal.lean

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
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker AutomorphicForm.CuspidalConstituent

open RealArchParam in

theorem LanglandsTunnell.ofReal_eq_laplaceEigenvalue_principal_of_archCasimirAt_eq_smul_of_mellin_eq_archFactor_principal
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
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (par₀ : ZMod 2)
    (hcen : LanglandsTunnell.Converse.IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) (default : InfinitePlace ℚ)
      ((RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent + 1)
      (((RealArchParam.principal u₁ a₁ u₂ a₂).centralSign.val : ℕ) : ℤ))
    (hMel : ∀ b : ZMod 2, (b = par₀ ∨ b = par₀ + (RealArchParam.principal u₁ a₁ u₂ a₂).centralSign) →
      ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
        MellinConvergent (fun t : ℝ => (Wr t + (-1 : ℂ) ^ b.val * Wr (-t)) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (Wr t + (-1 : ℂ) ^ b.val * Wr (-t)) / (t : ℂ)) s =
            ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).archFactor s)
    (lam : ℝ) (hsm : IsArchSmoothAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ)
    (hΩ : archCasimirAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ = (lam : ℂ) • φ) :
    (lam : ℂ) = (RealArchParam.principal u₁ a₁ u₂ a₂).laplaceEigenvalue := by sorry
