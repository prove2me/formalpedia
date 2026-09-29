-- Prove2me | Theorems.Thm_LanglandsTunnell_centralExponent_modulus_and_whittaker_ne_zero_of_mellin_archFactor_rat
-- name    : LanglandsTunnell.centralExponent_modulus_and_whittaker_ne_zero_of_mellin_archFactor_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/db856e25-05d1-5982-90a5-4371c8aacca7
-- title:
--   Archimedean calibration of ξ and non-vanishing of the Whittaker coefficient
-- statement:
--   Fix a Hecke eigensystem $\Theta$ over $\mathbb{Q}$ with complex coefficients (a nonzero level ideal together with families $a,b$ indexed by the finite places), a homomorphism $\xi$ from the group $Z$ attached to `productionPinsGeneral ℚ` into $\mathbb{C}^\times$, which by `Subgroup.topEquiv` is read as a character $\chi$ of the full idele group $(\mathbb{A}_\mathbb{Q})^\times$, and a real number $\sigma_0$ such that $\|\chi(x)\| = \mathrm{ideleNorm}(x)^{\sigma_0}$ for every idele $x$, where $\mathrm{ideleNorm}$ is the value of the distributive Haar character on the adeles. Let $A$ be a real archimedean parameter, i.e. either a principal datum $(u_1,a_1,u_2,a_2)$ with $u_i \in \mathbb{C}$ and $a_i \in \mathbb{Z}/2$, or a discrete datum $(u,k)$ with $k \ge 1$; its central exponent is $u_1+u_2$, resp. $2u$, and its central sign is $a_1+a_2$, resp. $k+1 \bmod 2$. Assume `IsArchCompAt` at the unique infinite place $w$ of $\mathbb{Q}$ for $\chi$ with exponent $A.\mathrm{centralExponent}+1$ and integer $A.\mathrm{centralSign}.\mathrm{val}$, that is, $\chi$ restricted to $(\mathbb{Q}_w)^\times$ through the archimedean unit embedding equals $\|x\|^{\,\mathrm{mult}(w)(A.\mathrm{centralExponent}+1)}(x/\|x\|)^{A.\mathrm{centralSign}.\mathrm{val}}$. Fix further $\mathrm{par} \in \mathbb{Z}/2$, a function $\varphi_0$ on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, functions $W_r$ indexed by the infinite places, and $C$ on (finite adeles) $\times \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ with $C(1,1)\neq 0$. Two hypotheses are imposed: a factorisation, namely that for every idele $a$ and every $g$ with trivial archimedean component (i.e. in the kernel of `glArch`), the Whittaker coefficient $\int \varphi_0(u(x)\,\mathrm{diag}(a,1)g)\,\psi_{\mathbb{Q}}(-x)\,d\nu(x)$, taken at $\alpha = 1$ with the standard additive character $\psi_\mathbb{Q}$ and the measure of `productionPinsGeneral ℚ`, equals $\bigl(\prod_w W_r(w)(a_w)\bigr)\,C(a_{\mathrm{fin}},g)$; and Mellin data, namely that for each $b \in \mathbb{Z}/2$ with $b = \mathrm{par}$ or $b = \mathrm{par}+A.\mathrm{centralSign}$ there is $s_0 \in \mathbb{R}$ such that for $\operatorname{re}(s) > s_0$ the Mellin transform of $t \mapsto (W_r(w_\infty)(t) + (-1)^{b}W_r(w_\infty)(-t))/t$ converges and equals the archimedean factor of $A$ twisted by $(0,b)$, a product of $\Gamma_\mathbb{R}$- and $\Gamma_\mathbb{C}$-factors. The conclusion is fourfold: $\sigma_0 = \operatorname{re}(A.\mathrm{centralExponent}+1)$; for every $z \in \mathbb{R}^\times$, transported to $(\mathbb{Q}_{w})^\times$ by the real isomorphism of the completion at the real place, $\|\chi(z)\| = |z|^{\sigma_0}$; there is $t \in \mathbb{R}^\times$ with $W_r(w_\infty)(t) \neq 0$; and the Whittaker coefficient of $\varphi_0$ at $\alpha = 1$ is not the zero function on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$.
--
--   This is the archimedean bookkeeping step in the construction of the input data for the converse theorem used in the Langlands–Tunnell argument: it identifies the exponent of the modulus of the central character with the real part of the shifted central exponent of the prescribed archimedean parameter, and deduces non-vanishing of the archimedean Whittaker function and hence of the global Whittaker coefficient from the fact that the prescribed Mellin transform is a product of Gamma factors. It feeds the assembly of a unitary shaped vector with factorised Whittaker function over $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_centralExponent_modulus_and_whittaker_ne_zero_of_mellin_archFactor_rat.lean

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
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

theorem LanglandsTunnell.centralExponent_modulus_and_whittaker_ne_zero_of_mellin_archFactor_rat
    (Θ : HeckeEigensystem ℚ ℂ) (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (σ₀ : ℝ)
    (hσ₀ : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖((ξ.comp Subgroup.topEquiv.symm.toMonoidHom x : ℂˣ) : ℂ)‖ = TateGlobal.ideleNorm ℚ x ^ σ₀)
    (A : RealArchParam)
    (hcen : LanglandsTunnell.Converse.IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) (default : InfinitePlace ℚ)
      (A.centralExponent + 1) (A.centralSign.val : ℤ))
    (par : ZMod 2) (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ)
    (C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hC : C 1 1 ≠ 0)
    (hfac : (∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
                whittakerCoefficient ℚ
                    (productionPinsGeneral ℚ)
                    NumberField.StandardAddChar.psiQ φ₀ 1 (diagOne a * g)
                  = (∏ w : InfinitePlace ℚ, Wr w (NumberField.InfinitePlace.Completion.extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
                      * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g))
    (hMel : ∀ b : ZMod 2, (b = par ∨ b = par + A.centralSign) →
      ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
        MellinConvergent (fun t : ℝ => (Wr default t + (-1 : ℂ) ^ b.val * Wr default (-t)) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (Wr default t + (-1 : ℂ) ^ b.val * Wr default (-t)) / (t : ℂ)) s
            = (A.twist 0 b).archFactor s) :
    σ₀ = (A.centralExponent + 1).re ∧
    (∀ z : ℝˣ, ‖(TateGlobal.archLocalChar (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) default
        (Units.map (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
          (IsTotallyReal.isReal (default : InfinitePlace ℚ))).symm.toMonoidHom z) : ℂ)‖ = |(z : ℝ)| ^ σ₀) ∧
    (∃ t : ℝˣ, Wr default ((t : ℝ) : ℂ) ≠ 0) ∧
    whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₀ 1 ≠ 0 := by sorry
