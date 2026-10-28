-- Prove2me | Theorems.Thm_OAI_Lech_PerfectDomainStages_frobenius_homology_conductor_bound
-- name    : OAI.Lech.PerfectDomainStages.frobenius_homology_conductor_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:13:24.5308+00:00
-- url     : https://prove2.me/theorems/5a6e5c57-8d30-44b5-8a86-b90fdda922c2
-- title:
--   OAI.Lech.PerfectDomainStages.frobenius_homology_conductor_bound: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.PerfectDomainStages`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter`, `open scoped TensorProduct ENNReal Topology`, `open Lech.Koszul`):
--
--   ```lean
--   lemma frobenius_homology_conductor_bound
--       (hdim : dimension D = h)
--       (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
--         (IsLocalRing.ResidueField D)))
--       (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F) :
--       ∃ a : D, a ≠ 0 ∧ ∀ n i, i < 0 →
--         Module.length D ((frobeniusComplex D p n F).homology i) ≤
--           Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj
--             (frobeniusComplex D p n F)).homology i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.IsFiniteHomologyComplex` and `OAI.Lech.complexQuotient` (definitions bundle `OAIQ032L005` of this split); `OAI.Lech.dimension` and `OAI.Lech.frobeniusComplex` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proof of `OAI.Lech.SeparableOrder.frobenius_homology_tendsto_zero` of this split imports it.
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
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped TensorProduct ENNReal Topology
namespace Lech.PerfectDomainStages
open Lech.Koszul
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [CharP K p] [CharP L p]

include K L in
lemma frobenius_homology_conductor_bound
    (hdim : dimension D = h)
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F) :
    ∃ a : D, a ≠ 0 ∧ ∀ n i, i < 0 →
      Module.length D ((frobeniusComplex D p n F).homology i) ≤
        Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj
          (frobeniusComplex D p n F)).homology i) := by
  sorry

end Lech.PerfectDomainStages

end

end OAI
end
