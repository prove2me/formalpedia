-- Prove2me | Theorems.Thm_OAI_Lech_SeparableOrder_frobenius_homology_tendsto_zero
-- name    : OAI.Lech.SeparableOrder.frobenius_homology_tendsto_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:15:52.041839+00:00
-- url     : https://prove2.me/theorems/37c41c3b-a873-4dd8-873e-28783bcb6dc2
-- title:
--   OAI.Lech.SeparableOrder.frobenius_homology_tendsto_zero: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.SeparableOrder`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex`, `open scoped TensorProduct`, `open Filter`, `open scoped ENNReal Topology`):
--
--   ```lean
--   theorem frobenius_homology_tendsto_zero
--       (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
--       (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
--         (IsLocalRing.ResidueField D)))
--       (hdD : Lech.dimension D = h)
--       (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : Lech.IsFiniteHomologyComplex D F)
--       (i : ℤ) (hi : i < 0) :
--       Tendsto (fun n : ℕ => ((Module.length D ((Lech.frobeniusComplex D p n F).homology i)).toNat : ℝ) /
--         ((p:ℝ)^n)^(Lech.dimension D)) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.IsFiniteHomologyComplex` (definitions bundle `OAIQ032L005` of this split); `OAI.Lech.dimension` and `OAI.Lech.frobeniusComplex` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proof of `OAI.Lech.CharP.dutta_limit_from_perfection` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace Lech.SeparableOrder
open Filter
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
theorem frobenius_homology_tendsto_zero
    (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (hdD : Lech.dimension D = h)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : Lech.IsFiniteHomologyComplex D F)
    (i : ℤ) (hi : i < 0) :
    Tendsto (fun n : ℕ => ((Module.length D ((Lech.frobeniusComplex D p n F).homology i)).toNat : ℝ) /
      ((p:ℝ)^n)^(Lech.dimension D)) atTop (𝓝 0) := by
  sorry
end Lech.SeparableOrder

end

end OAI
end
