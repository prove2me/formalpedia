-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryFamilyMemoNormalized_width
-- name    : OAI.EditApproximation.queryFamilyMemoNormalized_width
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:45:31.943336+00:00
-- url     : https://prove2.me/theorems/cf4189d0-d169-45fe-82ad-8432b063079d
-- title:
--   OAI.EditApproximation.queryFamilyMemoNormalized_width: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryFamilyMemoNormalized_width` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryFamilyNormalize.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryFamilyNormalize.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem queryFamilyMemoNormalized_width
--       (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q)
--       (B V : ℕ) (hB : base.length ≤ B) (hV : |semantic key| ≤ (V : ℚ)) :
--       (rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank) normalized key).width ≤
--         Nat.size V + 2 * (queryFamilyMemoRemaining (M := M) (J := J) (R := R)
--           (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q key * B + 1) + 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.SourceRanked.value` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.physicalFamilyRequestValue` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.familyBase_pos` (definitions bundle `OAIQ361V3Ea003` of this split); `OAI.EditApproximation.queryFamilyMemoNormalized` (definitions bundle `OAIQ361V3Ea004` of this split); `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.BinaryMemo`, `OAI.EditApproximation.PositionCounts`, `OAI.EditApproximation.bitWordValue` and `OAI.EditApproximation.refinementFactor` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.PhysicalEntry` and `OAI.EditApproximation.rankedBitProgramValue` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.ChargedPhysicalRequest` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.occurrenceBuild` (the published bundle `Def_EditApproxScheme_10`); `OAI.EditApproximation.ChargedPhysicalRequest.rank` and `OAI.EditApproximation.SourceRanked.rank` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.PhysicalFamilyScalarDraw`, `OAI.EditApproximation.PhysicalFamilyScalarKey`, `OAI.EditApproximation.QueryFamilyMemoKey`, `OAI.EditApproximation.physicalFamilyAnswer` and `OAI.EditApproximation.queryFamilyMemoRemaining` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proof of `OAI.EditApproximation.computedQueryMemoNormalized_width` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryFamilyNormalize.lean (declaration OAI.EditApproximation.queryFamilyMemoNormalized_width)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea004

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Family
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)
  (initial : PhysicalEntry M J target.length → ℕ)
  (ha : ∀ pass, pass ≤ passes → (a pass).value = refinementFactor (BinaryFraction.value (A pass)) F)
  (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
  (hp : target.length ≤ 2 ^ positionBits)
  (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
  (hc : ∀ entry, (coarse entry).1.value = initial entry)
  (ell : ℕ) (hell : 0 < ell) (hdelta : delta.value = 1 / (ell : ℚ) ^ 10)
  (base : List Bool) (hbase : bitWordValue base = ell ^ 10 + 1)

local notation "raw" => queryFamilyMemoRaw source target N P F exponent H Q eM eF hP hM hF
  A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw
local notation "reference" => SourceRanked.body ChargedPhysicalRequest.rank
  (physicalFamilyProgram source target N P F exponent H Q T S passes copies
    (fun pass => BinaryFraction.value (A pass)) multiplier tau.value eta.value kappa.value delta.value initial)
  (physicalFamilyAnswer target N P F exponent H Q passes copies draw)
local notation "semantic" => SourceRanked.value
  (physicalFamilyAnswer target N P F exponent H Q passes copies draw)
  (physicalFamilyRequestValue source target N P F exponent H Q T S passes copies
    (fun pass => BinaryFraction.value (A pass)) multiplier tau.value eta.value kappa.value delta.value initial hP draw)
local notation "normalized" => queryFamilyMemoNormalized source target N P F exponent H Q eM eF hP hM hF
  A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw
  base (familyBase_pos ell base hbase)

include ha hs ht hp htable hc hell hdelta in
theorem queryFamilyMemoNormalized_width
    (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q)
    (B V : ℕ) (hB : base.length ≤ B) (hV : |semantic key| ≤ (V : ℚ)) :
    (rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank) normalized key).width ≤
      Nat.size V + 2 * (queryFamilyMemoRemaining (M := M) (J := J) (R := R)
        (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q key * B + 1) + 1 := by
  sorry

end Family
end EditApproximation

end OAI
end
