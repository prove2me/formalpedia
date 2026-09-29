-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_isSchwartzBruhat_and_tateFourier_shellKernels_of_conductor_le
-- name    : LanglandsTunnell.RankinSelberg.isSchwartzBruhat_and_tateFourier_shellKernels_of_conductor_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/3b96cfdc-31dd-5a2b-bea5-b01f4fb2167c
-- title:
--   Schwartz–Bruhat cut-off kernels with prescribed local Fourier transforms
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$, write $\mathbb{Q}_p$ for the completion `p.adicCompletion ℚ` with its valuation $v$, and let the Fourier transform be `tateFourier` for the inverse $\psi_p^{-1}$ of the standard local additive character and the self-dual Haar measure, i.e. $\mathcal{F}g(y)=\int g(x)\,\psi_p^{-1}(xy)\,dx$, the field being given its Borel structure. Let $\chi,\xi,\omega,\theta_0:\mathbb{Q}_p^{\times}\to\mathbb{C}^{\times}$ be homomorphisms and $k_p,B,f,b$ natural numbers such that $\chi$ has conductor exponent $k_p$ and $\xi$ has conductor exponent $B$ in the sense of `HasConductorExponentAt` (trivial on the set of units $u$ with $v(u)=1$ and $v(u-1)\le \exp(-c)$, and for each $m<c$ nontrivial on the corresponding set at level $m$), while $\omega$ is trivial on the units congruent to $1$ modulo $\mathfrak p^{f}$ and $\theta_0$ on those congruent to $1$ modulo $\mathfrak p^{b}$, with $B<k_p$, $f\le k_p$ and $2b+1\le k_p$. Put $\theta=\theta_0\,(\chi\xi^{-1})^{2}$. Let $\varphi,\varphi_1:\mathbb{Q}_p\to\mathbb{C}$ satisfy $\varphi(u)=\mathcal{F}\bigl(x\mapsto \theta(x)\,[v(x)=1]\bigr)(-u)$ and $\varphi_1(y)=\omega^{-1}(y\,\varpi^{2k_p})$ when $v(y)=\exp(2k_p)$ and $\varphi_1(y)=0$ otherwise, where $\varpi$ is the chosen uniformiser unit `uniformizerUnit` and characters are extended by $0$ at $0$ via `charExt`. Then: $\varphi$ and $\varphi_1$ are Schwartz–Bruhat, that is locally constant with compact support; $\mathcal{F}\varphi(t)=\theta(t)$ for every unit $t$ with $v(t)=1$, and $\mathcal{F}\varphi(y)=0$ whenever $v(y)\neq 1$; $\mathcal{F}\varphi_1(ty)=\omega(t)\,\mathcal{F}\varphi_1(y)$ for all $y$ and all units $t$ with $v(t)=1$; $\mathcal{F}\varphi_1(y)\neq 0$ forces $v(y)\le \exp(-f)$; and if $\varphi(u)\neq 0$ and $\varphi_1(y)\neq 0$ then $y\neq 0$, $v(y^{-1})\le \exp(-f)$ and $v(y^{-1}u)\le \exp(-f)$.
--
--   This is the local construction of the cut-off test functions used in the Jacquet–Shalika argument on highly ramified $\varepsilon$-factors, here at the place $p$ and for the twisting data of the cubic-induction/converse-theorem step: one kernel whose Fourier transform is the prescribed character $\theta_0(\chi\xi^{-1})^2$ on the unit shell and zero elsewhere, and one $\omega$-equivariant shell kernel with support conditions linking $u$ and $y^{-1}$. It feeds the Rankin–Selberg pairing statement [`LanglandsTunnell.RankinSelberg.exists_mem_span_schwartzBruhat_fourier_unitShell_pairing_ne_zero_of_deepTwist_of_conductor_le`](thm.html#LanglandsTunnell.RankinSelberg.exists_mem_span_schwartzBruhat_fourier_unitShell_pairing_ne_zero_of_deepTwist_of_conductor_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_isSchwartzBruhat_and_tateFourier_shellKernels_of_conductor_le.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem LanglandsTunnell.RankinSelberg.isSchwartzBruhat_and_tateFourier_shellKernels_of_conductor_le
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (kp : ℕ) (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)
    (ξ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (B : ℕ) (hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p ξ B)
    (f : ℕ)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hωf : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p f, ω u = 1)
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (b : ℕ) (hcθ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, θ₀ u = 1)
    (hBk : B < kp) (hfk : f ≤ kp) (hbk : 2 * b + 1 ≤ kp)
    (φ φ₁ : p.adicCompletion ℚ → ℂ)
    (hφdef : letI := LanglandsTunnell.TateLocal.localBorel ℚ p
      φ = (fun u : p.adicCompletion ℚ =>
        tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p)
          (fun x : p.adicCompletion ℚ => if Valued.v x = 1 then charExt (θ₀ * (χ * ξ⁻¹) ^ 2) x else 0) (-u)))
    (hφ₁def : φ₁ = (fun y : p.adicCompletion ℚ =>
        if Valued.v y = WithZero.exp (((2 * kp : ℕ)) : ℤ) then
          charExt ω⁻¹ (y * ((NumberField.AdelicLevel.uniformizerUnit ℚ p ^ (2 * kp) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ))
        else 0)) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ p
    IsSchwartzBruhat φ ∧ IsSchwartzBruhat φ₁ ∧

      (∀ t : (p.adicCompletion ℚ)ˣ, Valued.v (t : p.adicCompletion ℚ) = 1 →
        tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ (t : p.adicCompletion ℚ) =
          (((θ₀ * (χ * ξ⁻¹) ^ 2) t : ℂˣ) : ℂ)) ∧
      (∀ y : p.adicCompletion ℚ, Valued.v y ≠ 1 →
        tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ y = 0) ∧

      (∀ t : (p.adicCompletion ℚ)ˣ, Valued.v (t : p.adicCompletion ℚ) = 1 → ∀ y : p.adicCompletion ℚ,
        tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ ((t : p.adicCompletion ℚ) * y) =
          ((ω t : ℂˣ) : ℂ) * tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ y) ∧
      (∀ y : p.adicCompletion ℚ, tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ y ≠ 0 →
        Valued.v y ≤ WithZero.exp (-(f : ℤ))) ∧

      (∀ u y : p.adicCompletion ℚ, φ u ≠ 0 → φ₁ y ≠ 0 →
        y ≠ 0 ∧ Valued.v y⁻¹ ≤ WithZero.exp (-(f : ℤ)) ∧ Valued.v (y⁻¹ * u) ≤ WithZero.exp (-(f : ℤ))) := by sorry
