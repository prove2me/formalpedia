-- Prove2me | Theorems.Thm_OAI_Lech_SourceGraded_exists_uniform_geometric_stableImage
-- name    : OAI.Lech.SourceGraded.exists_uniform_geometric_stableImage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:30:11.647624+00:00
-- url     : https://prove2.me/theorems/3a0acbfb-326f-4331-b388-541d22461c2a
-- title:
--   OAI.Lech.SourceGraded.exists_uniform_geometric_stableImage: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.SourceGraded`, with `open CategoryTheory CategoryTheory.Limits`, `open scoped ENNReal ZeroObject`, `open CategoryTheory`, `open scoped TensorProduct ModuleCat.Algebra`, `open CategoryTheory CategoryTheory.Limits CochainComplex`, `open scoped ModuleCat.Algebra`, `open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex`, `open CategoryTheory CategoryTheory.Limits HomologicalComplex`):
--
--   ```lean
--   lemma exists_uniform_geometric_stableImage (l b : ℤ)
--       (hp : ∀ j, Module.Projective R (F.X j))
--       (hfin : ∀ j, Module.Finite R (F.X j))
--       (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
--       (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic) :
--       ∃ MD : ℕ, ∀ M N : ℕ, ∀ hMN : M≤N, MD≤M → MD≤N-M → ∀ i : ℤ,
--         IsIso (homologyMap (geometricStructureMap I z hz F N) i ≫
--           factorThruImage (homologyMap ((TensorTotal.Right.functor F).map
--             (thickeningCechTransition I z hz hMN)) i))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.TensorTotal.Right.functor` (definitions bundle `OAIQ032L002` of this split); `OAI.Lech.SourceGraded.coordinate_mem` (definitions bundle `OAIQ032L003` of this split); `OAI.Lech.baseChangeFunctor` and `OAI.Lech.baseChangeFunctor_additive` (definitions bundle `OAIQ032L008` of this split); `OAI.Lech.FilteredCech.positive`, `OAI.Lech.SourceGraded.geometricStructureMap`, `OAI.Lech.SourceGraded.thickeningCech` and `OAI.Lech.SourceGraded.thickeningCechTransition` (definitions bundle `OAIQ032L012` of this split).
--
--   **Used by.** The proof of `OAI.Lech.ReesRoot.scalarHomology_value` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L008
import Definitions.Def_OAIQ032L012

section

attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex

namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ)

lemma exists_uniform_geometric_stableImage (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ MD : ℕ, ∀ M N : ℕ, ∀ hMN : M≤N, MD≤M → MD≤N-M → ∀ i : ℤ,
      IsIso (homologyMap (geometricStructureMap I z hz F N) i ≫
        factorThruImage (homologyMap ((TensorTotal.Right.functor F).map
          (thickeningCechTransition I z hz hMN)) i)) := by
  sorry
end Lech.SourceGraded

open CochainComplex CochainComplex.HomComplex
end

end OAI
end
