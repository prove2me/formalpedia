-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_localZeta_test
-- name    : GroundTheory.LocalField.exists_localZeta_test
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:17:44.676453+00:00
-- url     : https://prove2.me/theorems/469f8fdf-742a-4524-a89a-013b1627fabc
-- title:
--   Local Field: exists local Zeta test
-- statement:
--   The Local Field construction uses the exists local Zeta test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L474-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L474-L491

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
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
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
  (hχ : Continuous χ)
include hψ hψ1 hχ

theorem GroundTheory.LocalField.exists_localZeta_test {s : ℂ} (hs1 : -quasiCharExponent χ < s.re)
    (hs2 : s.re < 1 - quasiCharExponent χ) :
    ∃ g : K → ℂ, g ∈ schwartzBruhat K ∧ localZeta g χ s ≠ 0 ∧
      localZeta (localFourier (selfDualMeasure ψ) ψ g) χ⁻¹ (1 - s) * localLFactor χ s =
        localEpsilon χ ψ s * localZeta g χ s * localLFactor χ⁻¹ (1 - s) := by sorry
