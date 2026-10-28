-- Prove2me | Theorems.Thm_OAI_Lech_SourceGraded_finiteThickening_homology_zeroClass
-- name    : OAI.Lech.SourceGraded.finiteThickening_homology_zeroClass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:30:11.326038+00:00
-- url     : https://prove2.me/theorems/6dd49b55-1f58-47f7-b8d1-51cddd759d02
-- title:
--   OAI.Lech.SourceGraded.finiteThickening_homology_zeroClass: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.SourceGraded`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike`):
--
--   ```lean
--   lemma finiteThickening_homology_zeroClass (t M n : ℕ) :
--       ell.zeroClass ((finiteThickening I z hz t M).homology n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.TorsionLength` (definitions bundle `OAIQ032L000` of this split); `OAI.Lech.SourceGraded.finiteThickening` (definitions bundle `OAIQ032L012` of this split); `OAI.Lech.TorsionLength.DirectSumZero` and `OAI.Lech.TorsionLength.zeroClass` (definitions bundle `OAIQ032L017` of this split).
--
--   **Used by.** The proof of `OAI.Lech.ReesRoot.scalarHomology_value` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L012
import Definitions.Def_OAIQ032L017

section

attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I) (ell : TorsionLength I)
  (hds : ell.DirectSumZero) (hh : 0<h)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value
    (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
      a^h • ell.value (ModuleCat.of R (R ⧸ I)))
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] TwistedLocalization.piece TwistedLocalization.pieceMap
  TwistedLocalization.gradedMap ImageCech.mapTerm IdealGraded.polynomialMap

include hds hh hmu ha in
lemma finiteThickening_homology_zeroClass (t M n : ℕ) :
    ell.zeroClass ((finiteThickening I z hz t M).homology n) := by
  sorry

end Lech.SourceGraded

end

end OAI
end
