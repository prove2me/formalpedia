-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp
-- name    : LanglandsTunnell.TateLocal.measureReal_setOf_valued_le_exp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/c6af5524-678f-5dd0-9ff3-fd344e282b40
-- title:
--   Haar volume of the valuation balls of Kᵥ
-- statement:
--   Let $K$ be a number field and let $v$ be a height-one prime of its ring of integers $\mathcal{O}_K$, with $K_v =$ `v.adicCompletion K` the associated completion, carrying its canonical valuation `Valued.v` with values in $\mathrm{WithZero}(\mathrm{Multiplicative}\,\mathbb{Z})$, written multiplicatively via `WithZero.exp`. Equip $K_v$ with a measurable space structure that is the Borel structure of its topology, and let $\mu$ be an additive Haar measure on $K_v$. Then for every integer $k$ the real-valued measure of the ball $\{x \in K_v : \mathrm{v}(x) \le \exp k\}$ equals $(\mathrm{absNorm}\,\mathfrak{p}_v)^{k}$ times the real-valued measure of the valuation ring `v.adicCompletionIntegers K` $= \{x : \mathrm{v}(x) \le 1\}$, where $\mathrm{absNorm}\,\mathfrak{p}_v$ is the absolute norm of the ideal $v$, i.e. the cardinality of the residue field at $v$, regarded as a real number. Since the valuation is normalised so that a uniformiser has value $\exp(-1)$, the ball in question is $\varpi^{-k}\mathcal{O}_v$, so the assertion is the scaling law $\mu(\mathfrak{p}_v^{-k}) = (N v)^{k}\mu(\mathcal{O}_v)$, stated for the real-valued measure `μ.real` of both sides.
--
--   This is the standard volume computation for the fractional-ideal balls of a non-archimedean local field: multiplication by a uniformiser scales additive Haar measure by the modulus $(Nv)^{-1}$. It is the volume input for the local Fourier analysis of indicator functions of balls on $K_v$, and is used in the computation of local zeta integrals and of twisted integrals appearing in the local theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp.lean

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField

theorem LanglandsTunnell.TateLocal.measureReal_setOf_valued_le_exp (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (k : ℤ) :
    μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = (Ideal.absNorm v.asIdeal : ℝ) ^ k * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by sorry
