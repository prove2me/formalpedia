-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_one_one_eq_integral
-- name    : LanglandsTunnell.TateLocal.localZeta_one_one_eq_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/13d4b8b8-513d-512b-9c32-290e3fd3afbc
-- title:
--   Tate local zeta integral at trivial character and s=1
-- statement:
--   Let $K$ be a number field, $v$ a place of $K$ coming from a height-one prime of the ring of integers $\mathcal{O}_K$, and work on the completion $K_v$ equipped with a measurable-space structure that is the Borel structure of its topology; let $\mu$ be an additive Haar measure on $K_v$ and let $F : K_v \to \mathbb{C}$ be integrable with respect to $\mu$. The assertion is that the local zeta integral $\mathrm{localZeta}\ \mu\ F\ 1\ 1$ equals $\int_{K_v} F \, d\mu$. Here `localZeta` is, for a multiplicative character $\chi : K_v^\times \to \mathbb{C}^\times$ and $s \in \mathbb{C}$, the integral of $x \mapsto F(x)\,\mathrm{charExt}\,\chi\,x\,\cdot\,(\mathrm{modulus}\,x)^{s}$ against the measure `mulMeasure` $\mu$, where $\mathrm{modulus}\,x$ is $0$ for $x = 0$ and otherwise the value of the distributive Haar character at the unit $x$, $\mathrm{charExt}\,\chi$ extends $\chi$ by $0$ at the origin, and `mulMeasure` $\mu$ is the restriction of $\mu$ to the complement of $\{0\}$ weighted by the density $x \mapsto (\mathrm{modulus}\,x)^{-1}$ in $[0,\infty]$. The character taken is the trivial one, $\chi = 1$, and the exponent is $s = 1$.
--
--   This is the normalisation statement behind Tate's local theory: the multiplicative measure $d^\times x = |x|_v^{-1}\,d\mu(x)$ on $K_v^\times$ is set up so that the zeta integral at the trivial character and $s=1$ recovers the plain additive integral. It is used in the evaluation of the local zeta integral of the twisted local factor at $s=1$ in the unramified case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_localZeta_one_one_eq_integral.lean

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_Completion_Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem LanglandsTunnell.TateLocal.localZeta_one_one_eq_integral
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (F : v.adicCompletion K → ℂ) (hF : Integrable F μ) :
    LanglandsTunnell.TateLocal.localZeta μ F 1 1 = ∫ x, F x ∂μ := by sorry
