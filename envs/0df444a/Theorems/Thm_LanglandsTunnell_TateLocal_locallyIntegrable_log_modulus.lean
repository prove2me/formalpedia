-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_locallyIntegrable_log_modulus
-- name    : LanglandsTunnell.TateLocal.locallyIntegrable_log_modulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/043e95d4-b130-52ce-8479-ca82eaefb339
-- title:
--   Local integrability of log|y|ᵥ on a nonarchimedean completion
-- statement:
--   Let $K$ be a number field and let $v$ be a height-one prime of its ring of integers $\mathcal{O}_K$, with $v$-adic completion $K_v =$ `v.adicCompletion K`, equipped with a measurable space structure that is the Borel structure of its topology, and let $\mu$ be an additive Haar measure on $K_v$. For $a$ in a field, [`LanglandsTunnell.TateLocal.modulus a`](def/LanglandsTunnell_TateLocalZeta.html#L15) is the nonnegative real defined to be $0$ when $a = 0$ and otherwise the scaling factor `distribHaarChar` of the additive Haar measure under multiplication by the unit $a$; on $K_v$ this coincides with the nonnegative norm $\|a\|_{+}$, i.e. with the normalised $v$-adic absolute value. The assertion is that the real-valued function $y \mapsto \log(\text{modulus } y)$ on $K_v$ is locally integrable with respect to $\mu$, that is, every point of $K_v$ has a neighbourhood on which this function is integrable. (At $y = 0$ the value is $\log 0 = 0$ by Mathlib's convention for `Real.log`, so no separate treatment of the origin is needed in the statement.)
--
--   This is the local integrability of $\log|y|_v$ at a finite place, the basic analytic input for Tate-style local zeta integrals and for weighted orbital integrals with logarithmic weights: the only possible singularity is at the origin, where the shells $\{|y|_v = q_v^{-m}\}$ contribute a convergent series. It is used in the construction and estimation of weighted local orbital integrals and in bounds for integrals of $1 + |\log\|\cdot\||$ over compact subsets of $K_v$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_locallyIntegrable_log_modulus.lean

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_Completion_Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem LanglandsTunnell.TateLocal.locallyIntegrable_log_modulus
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] :
    LocallyIntegrable (fun y : v.adicCompletion K => Real.log (LanglandsTunnell.TateLocal.modulus y : ℝ)) μ := by sorry
