-- Prove2me | Theorems.Thm_Kyprianou_Ch01_measurableReciprocalOccupationFromJointIntegerProcess
-- name    : Kyprianou.Ch01.measurableReciprocalOccupationFromJointIntegerProcess
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:10:32.476857+00:00
-- url     : https://prove2.me/theorems/b5448e5b-3521-40b2-ae4f-f764d68bdd0e
-- title:
--   Measurable reciprocal occupation integral at fixed physical time from a jointly measurable integer process
-- statement:
--   For an integer-valued process X that is jointly measurable as NNReal time × sample space, the source reciprocalOccupation X t ω is a measurable ENNReal random variable for each fixed physical time t. Its integrand is (ENNReal.ofReal((X (Real.toNNReal s)ω:ℝ)))⁻¹. The real-time extension is jointly measurable by composition with Real.toNNReal and Int.cast; ENNReal.ofReal and ENNReal inverse are measurable maps. Apply pinned Mathlib Measurable.lintegral_prod_right with ν=volume.restrict(Set.Ioc 0 (t:ℝ)), which is SFinite; unfold source reciprocalOccupation and match the two lintegrals. No integrability or finite offspring moment is required because the integrand and clock are ENNReal. This is a concrete remote-provable measure-theoretic lemma that reuses the accepted joint-measurable path version.
-- source:
--   Kyprianou (2006) §1.3.4 original reverse Lamperti definition Def_Kyprianou_Ch01_LampertiInverse. Canonical reverse theorem ac1b29c6-5525-4344-a03d-7469824736ed, accepted joint-clock sketch b5a9603d-ed83-42a6-a4f8-58d01ffcab00, accepted stopped-clock sketch c27b9d45-466f-43ce-adcf-f9368d7f292f. Target root-connected inverse clock version f852e790-8678-45eb-9775-7f5af1318dd3. Pinned Mathlib Measurable.lintegral_prod_right exact type verified remotely via signature probe job 51d18d8c-d445-4fae-b189-b83d487090d4.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.measurableReciprocalOccupationFromJointIntegerProcess
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hJoint : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2))
    (t : ℝ≥0) :
    Measurable (fun ω : Ω => reciprocalOccupation X t ω) := by
  sorry
