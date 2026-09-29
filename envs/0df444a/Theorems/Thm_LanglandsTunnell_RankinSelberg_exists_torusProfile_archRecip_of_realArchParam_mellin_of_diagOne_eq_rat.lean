-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_torusProfile_archRecip_of_realArchParam_mellin_of_diagOne_eq_rat
-- name    : LanglandsTunnell.RankinSelberg.exists_torusProfile_archRecip_of_realArchParam_mellin_of_diagOne_eq_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/79fe3673-bb56-513c-994b-b0d68ecc1527
-- title:
--   Archimedean torus profile and reciprocal for Rankin–Selberg over ℚ
-- statement:
--   Fix a real archimedean parameter $A$ (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb{C}$, $a_i\in\mathbb{Z}/2$, or $\mathrm{discrete}(u,k)$ with $k\ge 1$), a parity $\mathrm{par}_0\in\mathbb{Z}/2$, a real $\sigma_0$, functions $W_{r,0}:\mathbb{R}\to\mathbb{C}$ and $W_{A,0}:\mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$, and $\chi:\mathbb{R}^\times\to\mathbb{C}$. Assume: in the principal case $\mathrm{par}_0=a_1$, $|\operatorname{Re}(u_1-u_2)|<1$, and either $\operatorname{Re}(u_1-u_2)=0$ or ($\operatorname{Im}(u_1-u_2)=0$ and $a_1=a_2$); $\sigma_0=\operatorname{Re}(\mathrm{centralExponent}(A)+1)$, the central exponent being $u_1+u_2$, resp. $2u$; if $A$ is principal with $a_1=a_2$ and $\mathrm{par}_0=a_1$ then $W_{r,0}(-t)=(-1)^{a_1}W_{r,0}(t)$; if $A$ is discrete then $W_{r,0}$ vanishes on $t<0$; for each $b$ equal to $\mathrm{par}_0$ or to $\mathrm{par}_0+\mathrm{centralSign}(A)$ there is $s_0$ such that for $\operatorname{Re}s>s_0$ the Mellin transform of $t\mapsto (W_{r,0}(t)+(-1)^bW_{r,0}(-t))/t$ converges at $s$ and equals the archimedean $\Gamma$-factor $\prod\Gamma_{\mathbb{R}}(s+\mu)\prod\Gamma_{\mathbb{C}}(s+\nu)$ attached to $A$ twisted by $(0,b)$; $W_{A,0}(\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)h)=e^{2\pi i x}W_{A,0}(h)$; $\|\chi(z)\|=|z|^{\sigma_0}$ and $W_{A,0}(zI\cdot h)=\chi(z)W_{A,0}(h)$; $W_{A,0}(\mathrm{diag}(t,1))=W_{r,0}(t)$; $W_{A,0}$ continuous; and $W_{r,0}$ not identically zero on units. Setting $W_A(h)=W_{A,0}(h)\,|\det h|^{-\sigma_0/2}$, the conclusion asserts the existence of $P:\mathbb{R}\to\mathbb{R}$, $x_0\in\mathbb{R}$ and $H_\infty:\mathbb{C}\to\mathbb{C}$ such that $P$ is measurable and nonnegative, $P$ is not almost everywhere zero, $W_A(\mathrm{diag}(a_1,a_2))\overline{W_A(\mathrm{diag}(a_1,a_2))}=P(a_1/a_2)$ for all $a_1\ne 0$, $a_2>0$, the function $y\mapsto P(y)|y|^{\sigma'-2}$ is integrable for every $\sigma'>x_0$, $H_\infty$ is analytic at every real point $\sigma'>-1$, $H_\infty(0)=0$, and $H_\infty(s)\cdot\bigl(\tfrac12\pi^{-s}\Gamma(s)\int_{\mathbb{R}}P(y)|y|^{s-2}\,dy\bigr)=1$ whenever $\operatorname{Re}s>\max(x_0,0)$.
--
--   This packages the archimedean input of the Rankin–Selberg integral over $\mathbb{Q}$: from a real archimedean parameter and a Whittaker function realising its $\Gamma$-factors, it produces the torus profile $P$ of $|W_A|^2$ on the diagonal, an abscissa of convergence for its Mellin integral, and a reciprocal $H_\infty$ vanishing at $0$ for the completed archimedean zeta integral. It feeds the construction of unitary shaped vectors with Whittaker factorisation in [`AutomorphicForm.exists_unitaryShapedVector_whittakerFactorization_torusProfile_of_isArithGenuineCuspRealizable_rat`](thm.html#AutomorphicForm.exists_unitaryShapedVector_whittakerFactorization_torusProfile_of_isArithGenuineCuspRealizable_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_torusProfile_archRecip_of_realArchParam_mellin_of_diagOne_eq_rat.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

open RealArchParam in

theorem LanglandsTunnell.RankinSelberg.exists_torusProfile_archRecip_of_realArchParam_mellin_of_diagOne_eq_rat
    (A : RealArchParam) (par₀ : ZMod 2) (σ₀ : ℝ)
    (Wr₀ : ℝ → ℂ) (WA₀ : GL (Fin 2) ℝ → ℂ) (χ : ℝˣ → ℂ)
    (hpar : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), A = RealArchParam.principal u₁ a₁ u₂ a₂ → par₀ = a₁)
    (hσ : σ₀ = (A.centralExponent + 1).re)
    (hlt : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), A = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (hunit : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), A = RealArchParam.principal u₁ a₁ u₂ a₂ →
      (u₁ - u₂).re = 0 ∨ ((u₁ - u₂).im = 0 ∧ a₁ = a₂))
    (hparity : ∀ (u₁ u₂ : ℂ) (a₁ : ZMod 2), A = RealArchParam.principal u₁ a₁ u₂ a₁ → par₀ = a₁ →
      ∀ t : ℝ, Wr₀ (-t) = (-1 : ℂ) ^ a₁.val * Wr₀ t)
    (hDSvan : ∀ (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n), A = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr₀ t = 0)
    (hMel : ∀ b : ZMod 2, (b = par₀ ∨ b = par₀ + A.centralSign) →
      ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
        MellinConvergent (fun t : ℝ => (Wr₀ t + (-1 : ℂ) ^ b.val * Wr₀ (-t)) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (Wr₀ t + (-1 : ℂ) ^ b.val * Wr₀ (-t)) / (t : ℂ)) s = (A.twist 0 b).archFactor s)
    (hWAN : ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
      WA₀ (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * x) * WA₀ h)
    (hχ : ∀ z : ℝˣ, ‖χ z‖ = |(z : ℝ)| ^ σ₀)
    (hZ : ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ), WA₀ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) = χ z * WA₀ h)
    (hdiag : ∀ t : ℝˣ, WA₀ (diagOne t) = Wr₀ (t : ℝ))
    (hWAc : Continuous WA₀)
    (hne : ∃ t : ℝˣ, Wr₀ (t : ℝ) ≠ 0) :
    let WA : GL (Fin 2) ℝ → ℂ := fun h => WA₀ h *
      (((|((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ)| ^ (-σ₀ / 2) : ℝ)) : ℂ)
    ∃ (P : ℝ → ℝ) (x₀ : ℝ) (Hinf : ℂ → ℂ),
      Measurable P ∧
      (∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
        WA (upperUnit a₁ 0 a₂ h₁ h₂.ne') * (starRingEnd ℂ) (WA (upperUnit a₁ 0 a₂ h₁ h₂.ne')) = ((P (a₁ / a₂) : ℝ) : ℂ)) ∧
      (∀ y : ℝ, 0 ≤ P y) ∧
      (¬ ∀ᵐ y : ℝ, P y = 0) ∧
      (∀ σ' : ℝ, x₀ < σ' → Integrable (fun y : ℝ => P y * |y| ^ (σ' - 2))) ∧
      (∀ σ' : ℝ, (-1 : ℝ) < σ' → AnalyticAt ℂ Hinf (σ' : ℂ)) ∧
      Hinf 0 = 0 ∧
      (∀ s : ℂ, max x₀ 0 < s.re →
        Hinf s * ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
          ∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ (s - 2)) = 1) := by sorry
