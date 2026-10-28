-- Prove2me | Theorems.Thm_OAI_Lech_exists_scalar_extension_homology_bound
-- name    : OAI.Lech.exists_scalar_extension_homology_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:17:46.074129+00:00
-- url     : https://prove2.me/theorems/e48c40b6-ee67-4b06-8956-cf75ba55c570
-- title:
--   OAI.Lech.exists_scalar_extension_homology_bound: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex`, `open scoped TensorProduct`):
--
--   ```lean
--   theorem exists_scalar_extension_homology_bound
--       [IsDomain R] [IsNoetherianRing R] [Module.Finite R S]
--       (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))) :
--       ∃ (r : ℕ) (g : R), g ≠ 0 ∧ ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
--         (∀ j,Function.Injective (fun x : (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F).X j =>
--           (algebraMap R S g) • x)) →
--         Module.length S ((((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F).homology i) ≠ ⊤ →
--         Module.length S ((((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F).homology i) ≤
--           r • Module.length R (F.homology i) +
--             Module.length S (((complexQuotient (Ideal.span {algebraMap R S g}) (.up ℤ)).obj
--               (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F)).homology i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.extendScalars_additive` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.complexQuotient` (definitions bundle `OAIQ032L005` of this split).
--
--   **Used by.** The proof of `OAI.Lech.FrobeniusIntermediate.frobenius_homology_order_transfer` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L004
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
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

theorem exists_scalar_extension_homology_bound
    [IsDomain R] [IsNoetherianRing R] [Module.Finite R S]
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))) :
    ∃ (r : ℕ) (g : R), g ≠ 0 ∧ ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
      (∀ j,Function.Injective (fun x : (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F).X j =>
        (algebraMap R S g) • x)) →
      Module.length S ((((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F).homology i) ≠ ⊤ →
      Module.length S ((((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F).homology i) ≤
        r • Module.length R (F.homology i) +
          Module.length S (((complexQuotient (Ideal.span {algebraMap R S g}) (.up ℤ)).obj
            (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F)).homology i) := by
  sorry
end Lech

end

end OAI
end
