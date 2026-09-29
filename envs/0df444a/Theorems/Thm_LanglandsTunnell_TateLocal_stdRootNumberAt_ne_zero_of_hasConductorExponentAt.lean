-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_ne_zero_of_hasConductorExponentAt
-- name    : LanglandsTunnell.TateLocal.stdRootNumberAt_ne_zero_of_hasConductorExponentAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/86088ac3-3674-547f-a731-829b2b46c77c
-- title:
--   Non-vanishing of the standard local root number at a ramified character
-- statement:
--   Let $K$ be a number field and $v$ a nonzero prime of its ring of integers $\mathcal{O}_K$, with completion $K_v =$ `v.adicCompletion K`. Let $\chi : K_v^\times \to \mathbb{C}^\times$ be a homomorphism of groups of units (no continuity is required), and let $a$ be a natural number with $1 \le a$. Assume `HasConductorExponentAt K v χ a`, i.e. (i) $\chi(u) = 1$ for every unit $u$ of $K_v$ with $|u|_v = 1$ and $|u - 1|_v \le q_v^{-a}$ in the sense $\mathrm{Valued.v}(u-1) \le \exp(-a)$, and (ii) for every $m < a$ there is a unit $u$ with $|u|_v = 1$ and ($m = 0$, or $\mathrm{Valued.v}(u-1) \le \exp(-m)$) such that $\chi(u) \ne 1$; thus $a$ is the exact conductor exponent, the case $m = 0$ imposing non-triviality on the full unit group. Assume moreover that $\lVert \chi(\varpi_v) \rVert = 1$, where $\varpi_v$ is the distinguished uniformizer unit `uniformizerUnit K v` of $K_v$, the image of the chosen uniformizer of $v$ in $\mathcal{O}_K$. Then `stdRootNumberAt K v χ`, the value at $s = 1/2$ of the local epsilon factor formed from the self-dual Haar measure `selfDualHaarAt K v`, the standard additive character `psiLocal K v` and the standard test function `stdTestFunAt K v χ`, is a nonzero complex number.
--
--   This is the local statement from Tate's theory that the epsilon factor of a ramified quasi-character, in the normalisation given by the standard test function and the self-dual measure, is a nonzero constant (essentially a Gauss sum times an elementary nonzero factor). It is used in the cubic-induction and Whittaker-model computations, where local root numbers at ramified places are multiplied together and must be inverted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_ne_zero_of_hasConductorExponentAt.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel

theorem LanglandsTunnell.TateLocal.stdRootNumberAt_ne_zero_of_hasConductorExponentAt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a) (hχ : HasConductorExponentAt K v χ a)
    (hu : ‖(χ (uniformizerUnit K v) : ℂ)‖ = 1) :
    stdRootNumberAt K v χ ≠ 0 := by sorry
