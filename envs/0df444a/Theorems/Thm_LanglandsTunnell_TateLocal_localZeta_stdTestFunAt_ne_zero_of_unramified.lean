-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_ne_zero_of_unramified
-- name    : LanglandsTunnell.TateLocal.localZeta_stdTestFunAt_ne_zero_of_unramified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/08ab780e-0666-500a-9461-5f3d351c5576
-- title:
--   Non-vanishing of the unramified local zeta integral
-- statement:
--   Let $K$ be a number field and $v$ a nonzero prime of its ring of integers, with completion $K_v$, valuation ring $\mathcal{O}_v$ and residue norm $Nv =$ `Ideal.absNorm v.asIdeal`. Let $\chi : K_v^\times \to \mathbb{C}^\times$ be a group homomorphism and $s \in \mathbb{C}$. Assume `HasConductorExponentAt K v χ 0`, i.e. $\chi$ is trivial on $\{u : \mathrm{val}(u) = 1\} = \mathcal{O}_v^\times$ (the second clause of that predicate is vacuous for $c = 0$), and assume $\lVert\chi(\varpi_v)\rVert \cdot Nv^{-\operatorname{Re} s} < 1$, where $\varpi_v$ is the unit `uniformizerUnit K v`, the image in $K_v$ of the chosen uniformiser of $v$. Then the local zeta integral is nonzero: with $|x|$ the module `modulus` of $K_v$, $\chi$ extended by $0$ at the origin, $d^\times x = |x|^{-1}\,d\mu$ on $K_v \setminus \{0\}$ and $\mu =$ `selfDualHaarAt K v` the additive Haar measure giving $\mathcal{O}_v$ mass $Nv^{-n/2}$, where $n$ is the level `addCharLevel` of the local component at $v$ of the standard additive character, one has $\int f(x)\,\chi(x)\,|x|^{s}\,d^\times x \neq 0$ for the test function $f =$ `stdTestFunAt K v χ`, which under the conductor hypothesis is the indicator function of $\mathcal{O}_v$.
--
--   This is the non-vanishing part of Tate's unramified local computation: in the region of absolute convergence the zeta integral of the indicator of $\mathcal{O}_v$ against an unramified quasi-character equals a positive measure times the local $L$-factor, hence never vanishes. It is used where local $\gamma$- and $\varepsilon$-factors are formed as quotients of zeta integrals of the standard test function, and is cited by [`LanglandsTunnell.CubicInduction.localZeta_tateFourier_mul_localLFactorAt_eq`](thm.html#LanglandsTunnell.CubicInduction.localZeta_tateFourier_mul_localLFactorAt_eq) and [`LanglandsTunnell.HeckeTate.isNicePinned_heckeDatum`](thm.html#LanglandsTunnell.HeckeTate.isNicePinned_heckeDatum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_ne_zero_of_unramified.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

theorem LanglandsTunnell.TateLocal.localZeta_stdTestFunAt_ne_zero_of_unramified
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) (hχ : HasConductorExponentAt K v χ 0)
    (hs : ‖(χ (uniformizerUnit K v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1) :
    localZeta (selfDualHaarAt K v) (stdTestFunAt K v χ) χ s ≠ 0 := by sorry
