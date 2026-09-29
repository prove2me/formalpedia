-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
-- name    : LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/3c4aff49-2251-55a3-b89c-534cd4fac38e
-- title:
--   The measure dx/|x|ᵥ is Haar on Kᵥ^×
-- statement:
--   Let $K$ be a number field, let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$ (a point of its height-one spectrum), and let $K_v$ denote the $v$-adic completion of $K$, equipped with a measurable structure which is the Borel structure of its topology. Let $\mu$ be an additive Haar measure on $K_v$, and equip the unit group $K_v^{\times}$ likewise with a measurable structure which is its Borel structure. Form the measure $\mathrm{mulMeasure}\ \mu$ on $K_v$: restrict $\mu$ to the complement of $\{0\}$ and take the density $x \mapsto (\mathrm{modulus}\ x)^{-1}$ with values in $[0,\infty]$, where $\mathrm{modulus}\ x$ is $0$ for $x = 0$ and otherwise the value at the unit $x$ of the distributive Haar character of $K_v$, i.e. the factor by which multiplication by $x$ scales additive Haar measure. The assertion is that the pullback (comap) of this measure along the inclusion $K_v^{\times} \to K_v$, $u \mapsto u.\mathrm{val}$, is a Haar measure of the multiplicative group $K_v^{\times}$: it is invariant under left translations, finite on compact sets, and positive on nonempty open sets.
--
--   This is the multiplicative Haar measure $d^{\times}x = dx/|x|_v$ of Tate's local theory, with no normalisation inserted (the modulus on $K_v$ being the $v$-adic absolute value, by [`LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm`](thm.html#LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm)). It is the measure against which the local zeta integrals and the Whittaker-model shell integrals at finite places are taken, and it is invoked throughout those computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure.lean

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_Completion_Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ] :
    (Measure.comap Units.val (mulMeasure μ) : Measure (v.adicCompletion K)ˣ).IsHaarMeasure := by sorry
