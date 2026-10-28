-- Prove2me | Theorems.Thm_OAI_Lech_ReesRoot_exceptionalZ_finite
-- name    : OAI.Lech.ReesRoot.exceptionalZ_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:32:20.429269+00:00
-- url     : https://prove2.me/theorems/85d276f0-2f05-413d-8a93-c0a95d2368f1
-- title:
--   OAI.Lech.ReesRoot.exceptionalZ_finite: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.ReesRoot`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory`, `open ProductSourceCover`):
--
--   ```lean
--   lemma exceptionalZ_finite (q : ℤ) : ell.finiteClass ((exceptionalZ I z hz m).homology q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.TorsionLength` (definitions bundle `OAIQ032L000` of this split); `OAI.Lech.ProductSourceCover.Chart` (definitions bundle `OAIQ032L007` of this split); `OAI.Lech.TorsionLength.DirectSumZero` and `OAI.Lech.TorsionLength.finiteClass` (definitions bundle `OAIQ032L017` of this split); `OAI.Lech.ReesRoot.exceptionalCech` and `OAI.Lech.ReesRoot.exceptionalZ` (definitions bundle `OAIQ032L035` of this split).
--
--   **Used by.** The proofs of `OAI.Lech.ReesRoot.layerAtTotal_finite`, `OAI.Lech.ReesRoot.thickeningZ_euler`, `OAI.Lech.ReesRoot.thickeningZ_finite` and `OAI.Lech.ReesRoot.unfilteredEuler_diagonal` of this split import it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L035

section

attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ} [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)
  (hgen : Ideal.span (Set.range z)=I) (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))

include hgen hds hmu ha in
lemma exceptionalZ_finite (q : ℤ) : ell.finiteClass ((exceptionalZ I z hz m).homology q) := by
  sorry

end Lech.ReesRoot

end

end OAI
end
