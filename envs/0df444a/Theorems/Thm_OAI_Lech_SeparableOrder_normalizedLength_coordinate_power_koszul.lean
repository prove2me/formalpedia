-- Prove2me | Theorems.Thm_OAI_Lech_SeparableOrder_normalizedLength_coordinate_power_koszul
-- name    : OAI.Lech.SeparableOrder.normalizedLength_coordinate_power_koszul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:42:34.885368+00:00
-- url     : https://prove2.me/theorems/2e833516-9936-4b29-8c0a-01ed1bd179cf
-- title:
--   OAI.Lech.SeparableOrder.normalizedLength_coordinate_power_koszul: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.SeparableOrder`, with `open MvPowerSeries`, `open scoped Classical`, `open scoped TensorProduct`, `open IsLocalRing`, `open MvPowerSeries IsLocalRing`, `open scoped ENNReal`, `open scoped ENNReal TensorProduct Classical DirectSum`, `open TensorProduct`, `open scoped TensorProduct nonZeroDivisors`, `open scoped nonZeroDivisors`, `open scoped BigOperators`, `open scoped nonZeroDivisors TensorProduct`, `open scoped Classical Pointwise`, `open CategoryTheory CategoryTheory.Limits`, `open CochainComplex CochainComplex.HomComplex`, `open scoped ENNReal ZeroObject`, `open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex`, `open CategoryTheory CategoryTheory.Limits HomologicalComplex`, `open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows`, `open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian`, `open Lech.RootTower Lech.PerfectDomainStages Lech.Koszul`, `open CategoryTheory CochainComplex HomologicalComplex`):
--
--   ```lean
--   theorem normalizedLength_coordinate_power_koszul (a : ℕ) (ha : a ≠ 0)
--       (i : ℤ) (hi : i < 0) :
--       normalizedLength (Fin h) k p
--         ((tensor (((List.ofFn (fun j : Fin h =>
--             (MvPowerSeries.X j : MvPowerSeries (Fin h) k)^a)).map
--             (PerfectClosure.of (MvPowerSeries (Fin h) k) p)).reverse)
--           (singleModule (ModuleCat.of (PerfectClosure (MvPowerSeries (Fin h) k) p)
--             (PerfectClosure D p)))).homology i) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.PerfectDomainStages.domainAlgebra` and `OAI.Lech.RootTower.powerSeriesCharP` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.Koszul.tensor` (definitions bundle `OAIQ032L005` of this split); `OAI.Lech.Koszul.singleModule` (definitions bundle `OAIQ032L006` of this split); `OAI.Lech.RootTower.normalizedLength` (definitions bundle `OAIQ032L023` of this split).
--
--   **Used by.** The proofs of `OAI.Lech.CharP.exists_length_with_module_limit` and `OAI.Lech.SeparableOrder.normalizedLength_perfection_shortComplex_homology` of this split import it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L023

section

attribute [-instance] _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech.SeparableOrder
open Lech.RootTower Lech.PerfectDomainStages Lech.Koszul
open CategoryTheory CochainComplex HomologicalComplex
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [CharP K p] [CharP L p]

include K L in

theorem normalizedLength_coordinate_power_koszul (a : ℕ) (ha : a ≠ 0)
    (i : ℤ) (hi : i < 0) :
    normalizedLength (Fin h) k p
      ((tensor (((List.ofFn (fun j : Fin h =>
          (MvPowerSeries.X j : MvPowerSeries (Fin h) k)^a)).map
          (PerfectClosure.of (MvPowerSeries (Fin h) k) p)).reverse)
        (singleModule (ModuleCat.of (PerfectClosure (MvPowerSeries (Fin h) k) p)
          (PerfectClosure D p)))).homology i) = 0 := by
  sorry
end Lech.SeparableOrder

end

end OAI
end
