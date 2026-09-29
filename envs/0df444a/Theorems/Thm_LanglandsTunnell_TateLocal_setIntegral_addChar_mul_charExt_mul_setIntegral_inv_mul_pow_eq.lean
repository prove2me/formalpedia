-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq
-- name    : LanglandsTunnell.TateLocal.setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/df41086d-76bd-5adf-926c-2f7bad662793
-- title:
--   Product of unit Gauss integrals of χ and χ⁻¹
-- statement:
--   Let $K$ be a number field, $v$ a finite place of $K$, i.e. a height-one prime of $\mathcal{O}_K$, and let $K_v$ denote the $v$-adic completion, equipped with a measurable structure for which the topology is Borel, and with an additive Haar measure $\mu$. Let $\psi$ be a $\mathbb{C}$-valued additive character of $K_v$ which is trivial on $\{x : \mathrm{v}(x) \le \exp(n)\}$ for an integer $n$ and is non-trivial at some point of $\{x : \mathrm{v}(x) \le \exp(n+1)\}$. Let $\chi : K_v^{\times} \to \mathbb{C}^{\times}$ be a homomorphism and $f \ge 1$ a natural number such that `HasConductorExponentAt K v χ f` holds: $\chi$ is trivial on the set of units $u$ with $\mathrm{v}(u) = 1$ and $\mathrm{v}(u-1) \le \exp(-f)$, while for each $m < f$ there is a unit $u$ with $\mathrm{v}(u) = 1$ and, when $m > 0$, $\mathrm{v}(u-1) \le \exp(-m)$ (no second condition when $m = 0$), with $\chi(u) \ne 1$. Let $c \in K_v$ satisfy $\mathrm{v}(c) = \exp(n+f)$. Writing `charExt χ` for the extension of $\chi$ to $K_v$ by $0$ at $0$, the assertion is that $$\Big(\int_{\mathrm{v}(u)=1} \psi(cu)\,\tilde\chi(u)\,d\mu\Big)\Big(\int_{\mathrm{v}(u)=1} \psi(cu)\,\widetilde{\chi^{-1}}(u)\,d\mu\Big)\, N(v)^{f} = \tilde\chi(-1)\,\mu(\mathcal{O}_v)^{2},$$ where $N(v)$ is the absolute norm of the prime ideal of $v$ and $\mu(\mathcal{O}_v)$ is the real-valued measure of the ring of integers of $K_v$.
--
--   This is the standard computation of the absolute value of a ramified local Gauss integral (root number) in Tate's local theory: the unit integrals attached to $\chi$ and to $\chi^{-1}$ against a twisted additive character multiply to $\chi(-1)\mu(\mathcal{O}_v)^2 N(v)^{-f}$. It feeds the local functional equation at ramified places used in the construction of the local zeta and Whittaker data for the cubic induction step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.setIntegral_addChar_mul_charExt_mul_setIntegral_inv_mul_pow_eq
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (f : ℕ) (hf : 1 ≤ f) (hχ : HasConductorExponentAt K v χ f)
    (c : v.adicCompletion K) (hc : Valued.v c = WithZero.exp (n + f)) :
    (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (c * u) * charExt χ u ∂μ) *
          (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (c * u) * charExt χ⁻¹ u ∂μ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ f =
      charExt χ (-1) *
        ((μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ) ^ 2 := by sorry
