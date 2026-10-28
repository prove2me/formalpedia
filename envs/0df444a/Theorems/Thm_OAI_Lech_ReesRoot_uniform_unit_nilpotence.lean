-- Prove2me | Theorems.Thm_OAI_Lech_ReesRoot_uniform_unit_nilpotence
-- name    : OAI.Lech.ReesRoot.uniform_unit_nilpotence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:33:16.833007+00:00
-- url     : https://prove2.me/theorems/5dff89a5-4e32-4067-bf2b-d2acaa38ea59
-- title:
--   OAI.Lech.ReesRoot.uniform_unit_nilpotence: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.ReesRoot`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂`):
--
--   ```lean
--   theorem uniform_unit_nilpotence
--       (hp : ∀ p,Module.Projective R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
--       (hflat : ∀ p,Module.Flat R (F.X p))
--       (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
--       (ha : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic) :
--       ∃ M : ℕ, 0<M ∧ ∀ m : Fin n → ℤ, ∀ i : ℤ,
--         homologyMap (total.map (enlargedPath I z hz F h s hd m 1 M) (.up ℤ)) i=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.ReesRoot.twistSequence` (definitions bundle `OAIQ032L007` of this split); `OAI.Lech.baseChangeFunctor` and `OAI.Lech.baseChangeFunctor_additive` (definitions bundle `OAIQ032L008` of this split); `OAI.Lech.ReesRoot.enlargedAt` (definitions bundle `OAIQ032L035` of this split); `OAI.Lech.ReesRoot.enlargedPath` (definitions bundle `OAIQ032L039` of this split).
--
--   **Used by.** The proofs of `OAI.Lech.ReesRoot.enlargedAtTotal_finite` and `OAI.Lech.ReesRoot.rootTotal_pure` of this split import it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L039

section

attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ) (hgen : Ideal.span (Set.range z)=I)

include hgen in

theorem uniform_unit_nilpotence
    (hp : ∀ p,Module.Projective R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
    (hflat : ∀ p,Module.Flat R (F.X p))
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
    (ha : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ M : ℕ, 0<M ∧ ∀ m : Fin n → ℤ, ∀ i : ℤ,
      homologyMap (total.map (enlargedPath I z hz F h s hd m 1 M) (.up ℤ)) i=0 := by
  sorry
end Lech.ReesRoot

end

end OAI
end
