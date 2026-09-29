-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_of_unramified
-- name    : LanglandsTunnell.TateLocal.localZeta_stdTestFunAt_eq_of_unramified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/71319676-7142-5c39-95ec-5b1ab42fae18
-- title:
--   Unramified local zeta integral equals μ(𝒪ᵥ^×) Lᵥ(χ,s)
-- statement:
--   Let $K$ be a number field, $v$ a maximal ideal of its ring of integers, $K_v$ the completion of $K$ at $v$ with valuation $\mathrm{v}$ and valuation ring $\mathcal{O}_v$, let $\chi : K_v^\times \to \mathbb{C}^\times$ be a homomorphism of groups and let $s \in \mathbb{C}$. Assume `HasConductorExponentAt K v χ 0`, i.e. $\chi$ is trivial on every unit $u$ of $K_v$ with $\mathrm{v}(u) = 1$ (the condition on smaller exponents is vacuous), and assume the convergence bound $\|\chi(\varpi_v)\| \cdot N v^{-\operatorname{Re} s} < 1$, where $\varpi_v$ is the image in $K_v^\times$ of the chosen uniformizer of $v$ (`uniformizerUnit`) and $Nv =$ `Ideal.absNorm v.asIdeal` is the residue cardinality. The measure used is `selfDualHaarAt K v`: the additive Haar measure of $K_v$ giving $\mathcal{O}_v$ mass $1$, scaled by $Nv^{-n/2}$, where $n$ is the level of the local component at $v$ of the standard adelic additive character, namely the supremum of the integers $m$ such that this character is trivial on $\{x : \mathrm{v}(x) \le \exp m\}$. Since the conductor hypothesis holds, the test function `stdTestFunAt K v χ` is the indicator function of $\mathcal{O}_v$. The assertion is that the local zeta integral $\int f(x)\,\chi(x)\,|x|^{s}$, taken with respect to the multiplicative measure obtained from `selfDualHaarAt K v` by restricting to $K_v \setminus \{0\}$ and multiplying by $|x|^{-1}$ (here $|\cdot|$ is the module `modulus`, $\chi$ extended by $0$ at $0$), equals the measure of $\{x : \mathrm{v}(x) = 1\}$ for `selfDualHaarAt K v`, viewed as a complex number, times `localLFactorAt K v χ s`, which under the conductor hypothesis is $(1 - \chi(\varpi_v) Nv^{-s})^{-1}$.
--
--   This is Tate's local computation at a finite place for an unramified quasi-character: in its region of absolute convergence the zeta integral of the indicator function of the valuation ring is the volume of the unit group times the local Euler factor. It is used for the non-vanishing of this zeta integral, for the local functional equation input to the cubic-induction Fourier identity, and in verifying the required properties of the Hecke datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_of_unramified.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem LanglandsTunnell.TateLocal.localZeta_stdTestFunAt_eq_of_unramified
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) (hχ : HasConductorExponentAt K v χ 0)
    (hs : ‖(χ (uniformizerUnit K v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1) :
    localZeta (selfDualHaarAt K v) (stdTestFunAt K v χ) χ s
      = ((selfDualHaarAt K v).real {x | Valued.v x = 1} : ℂ) * localLFactorAt K v χ s := by sorry
