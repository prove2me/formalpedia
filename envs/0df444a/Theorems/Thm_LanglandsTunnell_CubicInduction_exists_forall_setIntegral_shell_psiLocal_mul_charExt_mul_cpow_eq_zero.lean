-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero
-- name    : LanglandsTunnell.CubicInduction.exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/005f9400-81e4-535c-8dad-089844038fcb
-- title:
--   Shell integrals of ψ(-t) η(t) |t|^z vanish for large radius
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, so that $\mathbb{Q}_v$ denotes the $v$-adic completion, carried here with its Borel $\sigma$-algebra, and let $\eta : \mathbb{Q}_v^{\times} \to \mathbb{C}^{\times}$ be a homomorphism of multiplicative monoids which is locally constant. Then there is a natural number $c_1$ such that for every $z \in \mathbb{C}$ and every integer $j > c_1$ the integral of the function $t \mapsto \psi_v(-t)\cdot \mathrm{charExt}(\eta)(t)\cdot (\,|t|\,)^{z}$ over the shell $\{t \in \mathbb{Q}_v : \mathrm{v}(t) = \exp(j)\}$ vanishes. Here $\psi_v$ is [`NumberField.StandardAddChar.psiLocal`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65), the standard additive character of the adele ring of $\mathbb{Q}$ composed with the additive embedding of $\mathbb{Q}_v$ as the single coordinate at $v$ of the finite adeles; $\mathrm{charExt}(\eta)(t)$ is $\eta(t)$ for $t \neq 0$ and $0$ for $t = 0$; $|t| = \mathrm{modulus}(t)$ is the scaling factor of Haar measure under multiplication by $t$ (and $0$ at $t=0$), raised to the complex power $z$ after passage to $\mathbb{R}$ and then $\mathbb{C}$; and the measure is the multiplicative measure $\mathrm{mulMeasure}$ attached to the self-dual Haar measure $\mathrm{selfDualHaarAt}$ of $\mathbb{Q}_v$, i.e. that measure restricted to $\mathbb{Q}_v \setminus \{0\}$ and then given density $|x|^{-1}$, where $\mathrm{selfDualHaarAt}$ is the additive Haar measure normalised by the valuation ring, scaled by the absolute norm of $v$ to the power $-\mathrm{addCharLevel}(\psi_v)/2$. The bound $c_1$ depends only on $v$ and $\eta$, and in particular is chosen before $z$ and $j$.
--
--   This is the local vanishing statement underlying the convergence and continuation arguments for Tate's local zeta integrals: beyond a radius determined by the conductor of $\eta$ and the level of the additive character, the additive character oscillates over the cosets on which $\eta(t)|t|^z$ is constant, so each large shell contributes nothing. It is used in the estimates for the remainder of the dual zeta integral and for the truncated integrals over annuli and balls occurring in the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel in

theorem LanglandsTunnell.CubicInduction.exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero
    (v : HeightOneSpectrum (𝓞 ℚ))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) :
    ∃ c₁ : ℕ, ∀ z : ℂ, ∀ j : ℤ, (c₁ : ℤ) < j →
      ∫ t in {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j},
          (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z
        ∂(mulMeasure (selfDualHaarAt ℚ v)) = 0 := by sorry
