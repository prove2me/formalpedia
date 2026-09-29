-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one
-- name    : LanglandsTunnell.TateLocal.stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/a2d7974a-84c7-5606-87f9-b9138658f076
-- title:
--   Root numbers of χ and χ⁻¹ multiply to χ(-1)
-- statement:
--   Let $K$ be a number field, let $v$ be a prime of the ring of integers $\mathcal{O}_K$ (a point of the height-one spectrum), and let $\chi \colon (K_v)^\times \to \mathbb{C}^\times$ be a group homomorphism on the units of the $v$-adic completion $K_v$ of $K$. Let $a$ be a natural number with $1 \le a$, and assume `HasConductorExponentAt K v χ a`, i.e. $\chi$ is trivial on `higherUnitsAt K v a`, the set of units $u$ with $|u|_v = 1$ and $|u - 1|_v \le q_v^{-a}$ (where $|\cdot|_v$ is the `Valued` valuation and $q_v^{-a}$ denotes `WithZero.exp (-(a : ℤ))`), while for every $m < a$ there is a unit $u$ in `higherUnitsAt K v m` with $\chi(u) \ne 1$; for $m = 0$ the latter set is the full unit group of the valuation ring. Assume moreover that $|\chi(\pi_v)| = 1$, where $\pi_v$ is the unit `uniformizerUnit K v` of $K_v$ given by the image of the chosen uniformiser of $v$. Then $$\mathrm{stdRootNumberAt}(K,v,\chi) \cdot \mathrm{stdRootNumberAt}(K,v,\chi^{-1}) = \chi(-1),$$ where $\mathrm{stdRootNumberAt}(K,v,\chi)$ is the value at $s = 1/2$ of the local epsilon factor `stdEpsilonAt` formed from the self-dual Haar measure on $K_v$, the standard local additive character `psiLocal K v`, the standard test function `stdTestFunAt K v χ` and $\chi$, and $\chi^{-1}$ is the pointwise inverse character.
--
--   This is the local functional equation of Tate's theory evaluated at the centre of symmetry: $\varepsilon(s,\chi)\varepsilon(1-s,\chi^{-1}) = \chi(-1)$ read at $s = 1/2$, for a ramified character whose value at a uniformiser has absolute value one, so that the zeta integrals defining both epsilon factors converge there. It is used to show that the standard local root number has absolute value one, and in the computation of the local zeta integrals and Whittaker functionals occurring in the cubic-induction step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain

theorem LanglandsTunnell.TateLocal.stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a)
    (hu : ‖((χ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1) :
    stdRootNumberAt K v χ * stdRootNumberAt K v χ⁻¹ = ((χ (-1 : (v.adicCompletion K)ˣ) : ℂˣ) : ℂ) := by sorry
