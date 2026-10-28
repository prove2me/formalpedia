-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_flagMatrixDifference_dyadic_energy
-- name    : OAI.SimpleAmenable.flagMatrixDifference_dyadic_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:23:13.84607+00:00
-- url     : https://prove2.me/theorems/1fd02ff0-dcd8-47b7-b485-443a200ef1e8
-- title:
--   OAI.SimpleAmenable.flagMatrixDifference_dyadic_energy: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.flagMatrixDifference_dyadic_energy` of [lean/OAI/GroupTheory/SimpleAmenable/RandomFields/PolygonCovarianceEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/PolygonCovarianceEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`, `open Classical`):
--
--   ```lean
--   theorem flagMatrixDifference_dyadic_energy {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
--       (g : polygonFullGroup a m) (χ : (ℝ×ℝ) → ℝ)
--       (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1) {K L ρ η κ : ℝ}
--       (hK : 0<K) (hcompact : ∀x,K ≤ ‖x‖ → χ x=0)
--       (hL : 0≤L) (hρ : 0<ρ) (hη : 0<η) (hκ : 0<κ)
--       (hLip : ∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) :
--       ∃R C : ℝ,0≤R ∧ 0≤C ∧ ∀N : ℝ,1≤N → ∀I : Finset ℕ,
--         (∀i∈I,R ≤ κ/((2:ℝ)^i/N)) → ∀w : ℝ,
--         ∀T : Finset (FlagSite a m D v × FlagSite a m D v),
--         ∑p∈T,(w*∑i∈I,flagMatrixDifference hD g χ ρ N ((2:ℝ)^i) η κ p)^2 ≤
--           4*C*(I.card:ℝ)*w^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.TrackPoint` and `OAI.SimpleAmenable.polygonFullGroup` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.FlagSite` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.flagMatrixDifference` (definitions bundle `OAIQ65Sa014` of this split).
--
--   **Used by.** The proofs of `OAI_SimpleAmenable_FieldSignalData_realLaw_transport_constants` and `OAI.SimpleAmenable.finiteSignalFields_transport` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/PolygonCovarianceEnergy.lean (declaration OAI.SimpleAmenable.flagMatrixDifference_dyadic_energy)

import Mathlib
import Definitions.Def_OAIQ65Sa014

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonCovarianceEnergy
open Classical

theorem flagMatrixDifference_dyadic_energy {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (χ : (ℝ×ℝ) → ℝ)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1) {K L ρ η κ : ℝ}
    (hK : 0<K) (hcompact : ∀x,K ≤ ‖x‖ → χ x=0)
    (hL : 0≤L) (hρ : 0<ρ) (hη : 0<η) (hκ : 0<κ)
    (hLip : ∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) :
    ∃R C : ℝ,0≤R ∧ 0≤C ∧ ∀N : ℝ,1≤N → ∀I : Finset ℕ,
      (∀i∈I,R ≤ κ/((2:ℝ)^i/N)) → ∀w : ℝ,
      ∀T : Finset (FlagSite a m D v × FlagSite a m D v),
      ∑p∈T,(w*∑i∈I,flagMatrixDifference hD g χ ρ N ((2:ℝ)^i) η κ p)^2 ≤
        4*C*(I.card:ℝ)*w^2 := by
  sorry

end PolygonCovarianceEnergy

end SimpleAmenable
end
end

end OAI
end
