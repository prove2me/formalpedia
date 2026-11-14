-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_logRegularized_deriv_bound_of_completedXi_gap
-- name    : OAI.DukePrimeDegree.logRegularized_deriv_bound_of_completedXi_gap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:16:35.991381+00:00
-- url     : https://prove2.me/theorems/d1a66f5d-d72a-4024-9751-36c8a01b1cad
-- title:
--   OAI.DukePrimeDegree.logRegularized_deriv_bound_of_completedXi_gap: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.logRegularized_deriv_bound_of_completedXi_gap` of [lean/OAI/NumberTheory/DukePrimeDegree/Arithmetic/StarkZeros.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Arithmetic/StarkZeros.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open Filter Set MeasureTheory`, `open scoped Topology`, `open PrimeDegreePackets PrimeDegreePackets.AnalyticGrowth`):
--
--   ```lean
--   theorem logRegularized_deriv_bound_of_completedXi_gap
--       {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
--       (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
--       {c B L : ℝ} (hc : 0 < c) (hB : 0 < B)
--       (hL : L = Real.log |(NumberField.discr K : ℝ)|) (hL4 : 4 ≤ L)
--       (harch : ∀ s ∈ Icc (1 : ℝ) 2, |archimedeanZetaTerm (d + 1) s| ≤ B)
--       (hgap : ∀ z, completedThetaXi σ hn z = 0 →
--         c ^ 2 ≤ (L * (1 - z.re)) ^ 2 + (L * z.im) ^ 2) :
--       ∀ h ∈ Ioc (0 : ℝ) (4 / L),
--         |deriv (logRegularizedDedekindZeta K) h| ≤
--           (4 * (1 + 3 / c) ^ 2 * (3 + B) + B + 2) * L
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.archimedeanZetaTerm` and `OAI.PrimeDegreePackets.logRegularizedDedekindZeta` (definitions bundle `OAIQ244Duke012` of this split); `OAI.PrimeDegreePackets.OrderedEmbeddings` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.prime_degree_packet_equidistribution_of_real_zero_exclusion` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Arithmetic/StarkZeros.lean (declaration OAI.DukePrimeDegree.logRegularized_deriv_bound_of_completedXi_gap)

import Mathlib
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Module
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke011
import Definitions.Def_OAIQ244Duke012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Set MeasureTheory
open scoped Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.AnalyticGrowth
  PrimeDegreePackets.HeckeMellin

universe u

theorem logRegularized_deriv_bound_of_completedXi_gap
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
    {c B L : ℝ} (hc : 0 < c) (hB : 0 < B)
    (hL : L = Real.log |(NumberField.discr K : ℝ)|) (hL4 : 4 ≤ L)
    (harch : ∀ s ∈ Icc (1 : ℝ) 2, |archimedeanZetaTerm (d + 1) s| ≤ B)
    (hgap : ∀ z, completedThetaXi σ hn z = 0 →
      c ^ 2 ≤ (L * (1 - z.re)) ^ 2 + (L * z.im) ^ 2) :
    ∀ h ∈ Ioc (0 : ℝ) (4 / L),
      |deriv (logRegularizedDedekindZeta K) h| ≤
        (4 * (1 + 3 / c) ^ 2 * (3 + B) + B + 2) * L := by
  sorry

end DukePrimeDegree

end OAI
end
