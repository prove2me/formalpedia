-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_polygon_signal_approx_identity
-- name    : OAI.SimpleAmenable.polygon_signal_approx_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:26:27.518854+00:00
-- url     : https://prove2.me/theorems/3965be02-7851-4fcf-b6ab-e09c2aa76bbc
-- title:
--   OAI.SimpleAmenable.polygon_signal_approx_identity: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.polygon_signal_approx_identity` of [lean/OAI/GroupTheory/SimpleAmenable/RandomFields/PolygonApproxIdentity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/PolygonApproxIdentity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`, `open Classical`):
--
--   ```lean
--   theorem polygon_signal_approx_identity {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
--       (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ)
--       (hψ : ContDiff ℝ 2 ψ) (hsψ : HasCompactSupport ψ) (q K L : ℝ)
--       (hL : 0<L) (hKL : K+2 ≤ L)
--       (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
--       (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
--       (hχ₁ : ∀x,‖x‖ ≤ K+2 → χ x=1)
--       (hχc : ∀x,L ≤ ‖x‖ → χ x=0) :
--       ∃R Q Cv Ca : ℝ,0 ≤ R ∧ 0 ≤ Q ∧ 0 ≤ Cv ∧ 0 ≤ Ca ∧
--         ∀(N r η κ : ℝ) (hN : 1 ≤ N),Q ≤ N → 1 ≤ r → r ≤ N →
--           0<η → η ≤ 1 → 0<κ → 36 ≤ r*η → 1 ≤ 2*κ/(r/N) → R ≤ κ/(r/N) →
--           let J := flagBoxFinset (a:=a) (m:=m) (v:=v) hD
--             (mul_pos (lt_of_lt_of_le zero_lt_one hN) hL)
--           let h := flagSignalDifference (v:=v) hD g (fun x => q+ψ x) N
--           let e := fun z => (∑w∈J,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w)-h z
--           let δ := 38880/((D:ℝ)*Real.sqrt (r*η))
--           (∀z,z∉J → e z=0) ∧
--           ∑z∈J,(e z)^2 ≤ flagVolumeConstant m D L*(Cv*η*(1+δ)+Ca*δ)^2+
--             flagExceptionalConstant a m D L*(κ+r/N)*(flagRowSumConstant D*Ca)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.TrackPoint` and `OAI.SimpleAmenable.polygonFullGroup` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.flagRowSumConstant` and `OAI.SimpleAmenable.flagVolumeConstant` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.FlagSite` and `OAI.SimpleAmenable.flagBoxFinset` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.flagExceptionalConstant` (definitions bundle `OAIQ65Sa009` of this split); `OAI.SimpleAmenable.flagAveragingMatrix` (definitions bundle `OAIQ65Sa011` of this split); `OAI.SimpleAmenable.flagSignalDifference` (definitions bundle `OAIQ65Sa014` of this split).
--
--   **Used by.** The proofs of `OAI_SimpleAmenable_FieldSignalData_realLaw_transport_constants` and `OAI.SimpleAmenable.sourceFlagMatrix_inverse_signal` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/PolygonApproxIdentity.lean (declaration OAI.SimpleAmenable.polygon_signal_approx_identity)

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
section PolygonApproxIdentity
open Classical

theorem polygon_signal_approx_identity {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hsψ : HasCompactSupport ψ) (q K L : ℝ)
    (hL : 0<L) (hKL : K+2 ≤ L)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    (hχ₁ : ∀x,‖x‖ ≤ K+2 → χ x=1)
    (hχc : ∀x,L ≤ ‖x‖ → χ x=0) :
    ∃R Q Cv Ca : ℝ,0 ≤ R ∧ 0 ≤ Q ∧ 0 ≤ Cv ∧ 0 ≤ Ca ∧
      ∀(N r η κ : ℝ) (hN : 1 ≤ N),Q ≤ N → 1 ≤ r → r ≤ N →
        0<η → η ≤ 1 → 0<κ → 36 ≤ r*η → 1 ≤ 2*κ/(r/N) → R ≤ κ/(r/N) →
        let J := flagBoxFinset (a:=a) (m:=m) (v:=v) hD
          (mul_pos (lt_of_lt_of_le zero_lt_one hN) hL)
        let h := flagSignalDifference (v:=v) hD g (fun x => q+ψ x) N
        let e := fun z => (∑w∈J,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w)-h z
        let δ := 38880/((D:ℝ)*Real.sqrt (r*η))
        (∀z,z∉J → e z=0) ∧
        ∑z∈J,(e z)^2 ≤ flagVolumeConstant m D L*(Cv*η*(1+δ)+Ca*δ)^2+
          flagExceptionalConstant a m D L*(κ+r/N)*(flagRowSumConstant D*Ca)^2 := by
  sorry

end PolygonApproxIdentity

end SimpleAmenable
end
end

end OAI
end
