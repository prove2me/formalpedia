-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one
-- name    : LanglandsTunnell.TateLocal.norm_stdRootNumberAt_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/2e497b5a-938c-5689-980b-950692376aef
-- title:
--   Unitarity of the standard local root number at a ramified place
-- statement:
--   Let $K$ be a number field, let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$, and let $\chi \colon (K_v)^\times \to \mathbb{C}^\times$ be a multiplicative homomorphism from the units of the $v$-adic completion of $K$ to the nonzero complex numbers. Let $a$ be a natural number with $1 \le a$, and assume `HasConductorExponentAt K v χ a`, that is: $\chi$ is trivial on the set `higherUnitsAt K v a` of units $u$ with $|u|_v = 1$ and $|u - 1|_v \le \exp(-a)$, while for every $m < a$ there is a unit $u$ with $|u|_v = 1$ and ($m = 0$, or $|u - 1|_v \le \exp(-m)$) on which $\chi$ is nontrivial; so $a$ is exactly the conductor exponent of $\chi$, and $\chi$ is ramified. Assume moreover that $|\chi(\varpi_v)| = 1$, where $\varpi_v$ is the unit `uniformizerUnit K v` of $K_v$ obtained from the chosen uniformiser of $v$ in $\mathcal{O}_K$. The conclusion is that the complex absolute value of `stdRootNumberAt K v χ` equals $1$; here the standard local root number is the value at $s = 1/2$ of the local epsilon factor formed from the self-dual Haar measure on $K_v$, the local component at $v$ of the standard additive character, the standard test function attached to $\chi$, and $\chi$ itself.
--
--   This is the unitarity of Tate's local epsilon factor at the centre of symmetry for a ramified character whose value at a uniformiser has absolute value one; it is obtained from the inverse law $\varepsilon(\chi)\varepsilon(\chi^{-1}) = \chi(-1)$ together with the explicit evaluation of the local zeta integrals of the standard test function and of its Tate–Fourier transform. It feeds the computations of products of local root numbers used in the cubic induction step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain

theorem LanglandsTunnell.TateLocal.norm_stdRootNumberAt_eq_one
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a)
    (hu : ‖((χ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1) :
    ‖stdRootNumberAt K v χ‖ = 1 := by sorry
