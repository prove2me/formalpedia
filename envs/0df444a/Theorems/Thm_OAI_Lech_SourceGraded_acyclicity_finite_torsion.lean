-- Prove2me | Theorems.Thm_OAI_Lech_SourceGraded_acyclicity_finite_torsion
-- name    : OAI.Lech.SourceGraded.acyclicity_finite_torsion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:28:34.60969+00:00
-- url     : https://prove2.me/theorems/f398ca34-3ce4-4cee-892d-4298d7e1f4b0
-- title:
--   OAI.Lech.SourceGraded.acyclicity_finite_torsion: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.SourceGraded`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex`):
--
--   ```lean
--   theorem acyclicity_finite_torsion
--       (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
--       (ha : ∀ a : ℕ, 0<a → ell.value (ModuleCat.of R
--         (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^h • ell.value (ModuleCat.of R (R ⧸ I)))
--       (hK : ∀ a : ℕ, 1≤a → ∀ i : ℤ, i<0 →
--         ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
--       (hf : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
--       (hb : ∀ j, j < -(h:ℤ) ∨ 0<j → IsZero (F.X j))
--       (hacyc : ∀ j, ((baseChangeFunctor R (Localization.Away (z j))).mapHomologicalComplex _ |>.obj F).Acyclic) :
--       (∀ i, powerTorsion I (F.homology i) ∧ ell.value (F.homology i)≠⊤) ∧
--         (∀ i : ℤ, i≠0 → ell.value (F.homology i)=0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.TorsionLength` and `OAI.Lech.powerTorsion` (definitions bundle `OAIQ032L000` of this split); `OAI.Lech.baseChangeFunctor` and `OAI.Lech.baseChangeFunctor_additive` (definitions bundle `OAIQ032L008` of this split); `OAI.Lech.Koszul.unit` (definitions bundle `OAIQ032L014` of this split).
--
--   **Used by.** The proofs of `OAI.Lech.ReesRoot.scalarEuler_value` and `OAI.Lech.complex_estimate_allModule` of this split import it.
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
namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] [Nontrivial R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (F : CochainComplex (ModuleCat.{u} R) ℤ)
include hz in

theorem acyclicity_finite_torsion
    (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ, 0<a → ell.value (ModuleCat.of R
      (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^h • ell.value (ModuleCat.of R (R ⧸ I)))
    (hK : ∀ a : ℕ, 1≤a → ∀ i : ℤ, i<0 →
      ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
    (hf : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j < -(h:ℤ) ∨ 0<j → IsZero (F.X j))
    (hacyc : ∀ j, ((baseChangeFunctor R (Localization.Away (z j))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    (∀ i, powerTorsion I (F.homology i) ∧ ell.value (F.homology i)≠⊤) ∧
      (∀ i : ℤ, i≠0 → ell.value (F.homology i)=0) := by
  sorry

end Lech.SourceGraded

end

end OAI
end
