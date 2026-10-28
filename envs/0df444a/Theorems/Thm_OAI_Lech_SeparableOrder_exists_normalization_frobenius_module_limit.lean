-- Prove2me | Theorems.Thm_OAI_Lech_SeparableOrder_exists_normalization_frobenius_module_limit
-- name    : OAI.Lech.SeparableOrder.exists_normalization_frobenius_module_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:42:06.448993+00:00
-- url     : https://prove2.me/theorems/4e37d1c2-c2c0-4439-8619-a8a49e7e44db
-- title:
--   OAI.Lech.SeparableOrder.exists_normalization_frobenius_module_limit: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.SeparableOrder`, with `open CategoryTheory`, `open scoped TensorProduct`, `open Lech.RootTower Lech.PerfectDomainStages Filter`, `open scoped ENNReal Topology`):
--
--   ```lean
--   theorem exists_normalization_frobenius_module_limit
--       (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
--       (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
--         (IsLocalRing.ResidueField D))) :
--       ∃ r : ℕ, 0 < r ∧ ∀ (M : ModuleCat.{u} D), IsFiniteLength D M →
--         Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*h))⁻¹ *
--           (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal)
--           atTop (𝓝 ((r : ℝ≥0∞) * normalizedLength (Fin h) k p
--             ((PerfectClosure D p) ⊗[D] M)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.FrobeniusModule`, `OAI.Lech.PerfectDomainStages.domainAlgebra`, `OAI.Lech.RootTower.perfectAlgebra` and `OAI.Lech.RootTower.powerSeriesCharP` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.RootTower.normalizedLength` (definitions bundle `OAIQ032L023` of this split).
--
--   **Used by.** The proof of `OAI.Lech.CharP.exists_length_with_module_limit` of this split imports it.
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
open CategoryTheory
open scoped TensorProduct
namespace Lech.SeparableOrder
open Lech.RootTower Lech.PerfectDomainStages Filter
open scoped ENNReal Topology
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [CharP K p] [CharP L p]

include K L in

theorem exists_normalization_frobenius_module_limit
    (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D))) :
    ∃ r : ℕ, 0 < r ∧ ∀ (M : ModuleCat.{u} D), IsFiniteLength D M →
      Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*h))⁻¹ *
        (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal)
        atTop (𝓝 ((r : ℝ≥0∞) * normalizedLength (Fin h) k p
          ((PerfectClosure D p) ⊗[D] M))) := by
  sorry
end Lech.SeparableOrder

end

end OAI
end
