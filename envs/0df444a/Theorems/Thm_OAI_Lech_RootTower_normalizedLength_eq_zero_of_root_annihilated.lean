-- Prove2me | Theorems.Thm_OAI_Lech_RootTower_normalizedLength_eq_zero_of_root_annihilated
-- name    : OAI.Lech.RootTower.normalizedLength_eq_zero_of_root_annihilated
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:41:25.09723+00:00
-- url     : https://prove2.me/theorems/d1269e51-1747-4f2a-a1d0-9d165008ecda
-- title:
--   OAI.Lech.RootTower.normalizedLength_eq_zero_of_root_annihilated: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.RootTower`, with `open MvPowerSeries`, `open scoped Classical`, `open scoped TensorProduct`, `open IsLocalRing`, `open MvPowerSeries IsLocalRing`, `open scoped ENNReal`, `open scoped ENNReal TensorProduct Classical DirectSum`, `open TensorProduct`, `open scoped TensorProduct nonZeroDivisors`, `open scoped nonZeroDivisors`, `open scoped BigOperators`, `open scoped nonZeroDivisors TensorProduct`, `open Filter`, `open scoped ENNReal Topology TensorProduct nonZeroDivisors`):
--
--   ```lean
--   lemma normalizedLength_eq_zero_of_root_annihilated
--       (M : Type*) [AddCommGroup M] [Module (PerfectClosure (MvPowerSeries (Fin h) k) p) M]
--       (H : Ideal (MvPowerSeries (Fin h) k))
--       (hH : H.radical = IsLocalRing.maximalIdeal (MvPowerSeries (Fin h) k))
--       {g : MvPowerSeries (Fin h) k} (hg : g ≠ 0)
--       (hHM : ∀ a ∈ H, ∀ x : M, PerfectClosure.of (MvPowerSeries (Fin h) k) p a • x = 0)
--       (hgM : ∀ n x, rootMap (MvPowerSeries (Fin h) k) p n g • (x : M) = 0) :
--       normalizedLength (Fin h) k p M = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.RootTower.powerSeriesCharP` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.RootTower.rootMap` (definitions bundle `OAIQ032L006` of this split); `OAI.Lech.RootTower.normalizedLength` (definitions bundle `OAIQ032L023` of this split).
--
--   **Used by.** The proof of `OAI.Lech.SeparableOrder.normalizedLength_coordinate_power_koszul` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L023

section

attribute [-instance] _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct

namespace Lech.RootTower
open Filter
open scoped ENNReal Topology TensorProduct nonZeroDivisors
variable (h : ℕ) (k : Type*) [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]

lemma normalizedLength_eq_zero_of_root_annihilated
    (M : Type*) [AddCommGroup M] [Module (PerfectClosure (MvPowerSeries (Fin h) k) p) M]
    (H : Ideal (MvPowerSeries (Fin h) k))
    (hH : H.radical = IsLocalRing.maximalIdeal (MvPowerSeries (Fin h) k))
    {g : MvPowerSeries (Fin h) k} (hg : g ≠ 0)
    (hHM : ∀ a ∈ H, ∀ x : M, PerfectClosure.of (MvPowerSeries (Fin h) k) p a • x = 0)
    (hgM : ∀ n x, rootMap (MvPowerSeries (Fin h) k) p n g • (x : M) = 0) :
    normalizedLength (Fin h) k p M = 0 := by
  sorry
end Lech.RootTower

open scoped Classical Pointwise
end
end

end OAI
end
