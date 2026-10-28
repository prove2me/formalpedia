-- Prove2me | Theorems.Thm_OAI_Lech_complex_estimate_allModule
-- name    : OAI.Lech.complex_estimate_allModule
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:30:56.742237+00:00
-- url     : https://prove2.me/theorems/0897fca5-4966-4b2f-ada9-45098da240cf
-- title:
--   OAI.Lech.complex_estimate_allModule: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex Lech.ProductSourceCover`, `open scoped ENNReal`):
--
--   ```lean
--   theorem complex_estimate_allModule (d : ℕ) (hd : 0<d) :
--       ∃ A : ℝ,0≤A ∧ ∀ {C : Type u} [CommRing C] [Nontrivial C]
--         (z : Fin d → C) (ell : AllModuleLength C) (e : ℝ) (_he : 0≤e)
--         (_hmu : ell.value (ModuleCat.of C (C ⧸ Ideal.span (Set.range z))) = ENNReal.ofReal e)
--         (_ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of C
--           (C ⧸ Ideal.span (Set.range (fun j => z j^a)))) = (a:ℝ≥0∞)^d*ENNReal.ofReal e)
--         (_hK : ∀ a : ℕ,1≤a → ∀ i : ℤ,i < 0 →
--           ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
--         (F : CochainComplex (ModuleCat.{u} C) ℤ)
--         (_hf : ∀ i,Module.Free C (F.X i)) (_hfin : ∀ i,Module.Finite C (F.X i))
--         (_hb : ∀ i,i < -(d:ℤ) ∨ 0 < i → IsZero (F.X i))
--         (_hac : ∀ j,(((baseChangeFunctor C (Localization.Away (z j))).mapHomologicalComplex _).obj F).Acyclic)
--         (s : ℕ) (_hs : 0 < s)
--         (_hδ : ∀ i : ℤ,(F.d i (i+1)).hom.range ≤
--           (Ideal.span (Set.range z))^s • (⊤ : Submodule C (F.X (i+1))))
--         (_halt : ∑ i∈Finset.range (d+1),(-1:ℝ)^i*(Module.finrank C (F.X (-(i:ℤ))):ℝ)=0),
--         e*(s:ℝ)^d*((Module.finrank C (F.X 0):ℝ)-A/s*
--           ∑ i∈Finset.range (d+1),(Module.finrank C (F.X (-(i:ℤ))):ℝ)) ≤
--             (ell.value (F.homology 0)).toReal
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.AllModuleLength` (definitions bundle `OAIQ032L000` of this split); `OAI.Lech.baseChangeFunctor` and `OAI.Lech.baseChangeFunctor_additive` (definitions bundle `OAIQ032L008` of this split); `OAI.Lech.Koszul.unit` (definitions bundle `OAIQ032L014` of this split).
--
--   **Used by.** The proof of `OAI.Lech.CharP.dutta_minimal_estimate` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L008
import Definitions.Def_OAIQ032L014

section

attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Lech.ProductSourceCover
open scoped ENNReal
namespace Lech
universe u

theorem complex_estimate_allModule (d : ℕ) (hd : 0<d) :
    ∃ A : ℝ,0≤A ∧ ∀ {C : Type u} [CommRing C] [Nontrivial C]
      (z : Fin d → C) (ell : AllModuleLength C) (e : ℝ) (_he : 0≤e)
      (_hmu : ell.value (ModuleCat.of C (C ⧸ Ideal.span (Set.range z))) = ENNReal.ofReal e)
      (_ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of C
        (C ⧸ Ideal.span (Set.range (fun j => z j^a)))) = (a:ℝ≥0∞)^d*ENNReal.ofReal e)
      (_hK : ∀ a : ℕ,1≤a → ∀ i : ℤ,i < 0 →
        ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
      (F : CochainComplex (ModuleCat.{u} C) ℤ)
      (_hf : ∀ i,Module.Free C (F.X i)) (_hfin : ∀ i,Module.Finite C (F.X i))
      (_hb : ∀ i,i < -(d:ℤ) ∨ 0 < i → IsZero (F.X i))
      (_hac : ∀ j,(((baseChangeFunctor C (Localization.Away (z j))).mapHomologicalComplex _).obj F).Acyclic)
      (s : ℕ) (_hs : 0 < s)
      (_hδ : ∀ i : ℤ,(F.d i (i+1)).hom.range ≤
        (Ideal.span (Set.range z))^s • (⊤ : Submodule C (F.X (i+1))))
      (_halt : ∑ i∈Finset.range (d+1),(-1:ℝ)^i*(Module.finrank C (F.X (-(i:ℤ))):ℝ)=0),
      e*(s:ℝ)^d*((Module.finrank C (F.X 0):ℝ)-A/s*
        ∑ i∈Finset.range (d+1),(Module.finrank C (F.X (-(i:ℤ))):ℝ)) ≤
          (ell.value (F.homology 0)).toReal := by
  sorry
end Lech

end

end OAI
end
