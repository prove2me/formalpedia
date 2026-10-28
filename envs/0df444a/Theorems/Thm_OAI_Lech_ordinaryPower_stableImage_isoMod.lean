-- Prove2me | Theorems.Thm_OAI_Lech_ordinaryPower_stableImage_isoMod
-- name    : OAI.Lech.ordinaryPower_stableImage_isoMod
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:33:42.83754+00:00
-- url     : https://prove2.me/theorems/ae93c9fb-8b41-41c4-8f1e-99153d3bb6a7
-- title:
--   OAI.Lech.ordinaryPower_stableImage_isoMod: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech`, with `open CategoryTheory CategoryTheory.Limits`, `open scoped ENNReal ZeroObject`, `open CategoryTheory`, `open scoped TensorProduct ModuleCat.Algebra`, `open CategoryTheory CategoryTheory.Limits CochainComplex`, `open scoped ModuleCat.Algebra`, `open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex`, `open CochainComplex CochainComplex.HomComplex`, `open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex`, `open CategoryTheory CategoryTheory.Limits HomologicalComplex`, `open scoped BigOperators`, `open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex`, `open Koszul`):
--
--   ```lean
--   lemma ordinaryPower_stableImage_isoMod
--       (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
--       (F : CochainComplex (ModuleCat.{u} R) ℤ)
--       [∀ j, Module.Free R (F.X j)] [∀ j, Module.Finite R (F.X j)]
--       (n : ℤ) (d : ℕ) (hsupp : ∀ i, i < n ∨ n+d ≤ i → IsZero (F.X i))
--       (h : ℕ) (z : Fin h → R) (t : ℕ) (ht : 1 ≤ t)
--       (H : ∀ j, Homotopy (z j ^ t • 𝟙 F) 0)
--       (hKos : ∀ a : ℕ, 1 ≤ a → ∀ i : ℤ, i < 0 → P ((unit (List.ofFn fun j => z j ^ a)).homology i)) :
--       ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∃ N₀ : ℕ, ∃ hMN₀ : M ≤ N₀,
--         ∀ N : ℕ, ∀ hN : N₀ ≤ N, ∀ i : ℤ,
--           P.isoModSerre (homologyMap
--             (complexQuotientπ (Ideal.span (Set.range z) ^ N) F) i ≫
--               factorThruImage (homologyMap
--                 ((complexQuotientMap (Ideal.pow_le_pow_right
--                   (hMN₀.trans hN))
--                   (.up ℤ)).app F) i))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.complexQuotient`, `OAI.Lech.complexQuotientMap` and `OAI.Lech.complexQuotientπ` (definitions bundle `OAIQ032L005` of this split); `OAI.Lech.Koszul.unit` (definitions bundle `OAIQ032L014` of this split).
--
--   **Used by.** The proof of `OAI.Lech.ReesRoot.scalarHomology_value` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L014

section

attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex

open scoped BigOperators

namespace Lech
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open Koszul
universe u
variable {R : Type u} [CommRing R]

lemma ordinaryPower_stableImage_isoMod
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ j, Module.Free R (F.X j)] [∀ j, Module.Finite R (F.X j)]
    (n : ℤ) (d : ℕ) (hsupp : ∀ i, i < n ∨ n+d ≤ i → IsZero (F.X i))
    (h : ℕ) (z : Fin h → R) (t : ℕ) (ht : 1 ≤ t)
    (H : ∀ j, Homotopy (z j ^ t • 𝟙 F) 0)
    (hKos : ∀ a : ℕ, 1 ≤ a → ∀ i : ℤ, i < 0 → P ((unit (List.ofFn fun j => z j ^ a)).homology i)) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∃ N₀ : ℕ, ∃ hMN₀ : M ≤ N₀,
      ∀ N : ℕ, ∀ hN : N₀ ≤ N, ∀ i : ℤ,
        P.isoModSerre (homologyMap
          (complexQuotientπ (Ideal.span (Set.range z) ^ N) F) i ≫
            factorThruImage (homologyMap
              ((complexQuotientMap (Ideal.pow_le_pow_right
                (hMN₀.trans hN))
                (.up ℤ)).app F) i)) := by
  sorry

end Lech
end
end

end OAI
end
