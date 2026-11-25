-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localZeta_eq_sum
-- name    : GroundTheory.LocalField.localZeta_eq_sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:06:45.383706+00:00
-- url     : https://prove2.me/theorems/75e0e05f-64fe-57a7-ab3a-08cb2cacb223
-- title:
--   Local Field: local Zeta eq sum
-- statement:
--   The Local Field construction uses the local Zeta eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaIntegral.lean#L210-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaIntegral.lean#L210-L283

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
variable {f : K → ℂ} {χ : Kˣ →* ℂˣ}
open scoped Classical

theorem GroundTheory.LocalField.localZeta_eq_sum (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) {M N : ℤ} (hMN : M ≤ N)
    (hM : ∀ x, f x ≠ 0 → x ∈ valBall K M) (hN : ∀ x ∈ valBall K N, f x = f 0) {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    localZeta f χ s =
      ∑ k ∈ Finset.Ico M N, (∫ u in ordShell K k, f u * ((χ u : ℂˣ) : ℂ) ∂multHaar K) *
          ((residueCard K : ℂ) ^ (-s)) ^ k +
        if IsUnramifiedChar χ then
          f 0 * (((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)) ^ N *
            (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹
        else 0 := by sorry
