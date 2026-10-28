-- Prove2me | Theorems.Thm_OAI_Lech_ReesRoot_quotientAtTotal_euler
-- name    : OAI.Lech.ReesRoot.quotientAtTotal_euler
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:37:00.116655+00:00
-- url     : https://prove2.me/theorems/00539ed4-cf94-4673-8e30-e484048b5fbf
-- title:
--   OAI.Lech.ReesRoot.quotientAtTotal_euler: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.ReesRoot`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ MonoidalCategory`, `open ProductSourceCover`):
--
--   ```lean
--   lemma quotientAtTotal_euler (N : ℕ) (hN : h+n≤N) :
--       finiteHomologyEuler ell ((quotientAt I z hz F h s hd m).total (.up ℤ)) (-(h:ℤ)) N=
--         ∑ k∈Finset.range (h+1),(-1:ℝ)^k*(b (-(h:ℤ)+k):ℝ)*
--           ∑ j∈Finset.range (IdealFiltered.order h s (-(h:ℤ)+k)),
--             finiteHomologyEuler ell (exceptionalZ I z hz (raise m j)) 0 n
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.TorsionLength` (definitions bundle `OAIQ032L000` of this split); `OAI.Lech.IdealFiltered.order` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.ProductSourceCover.Chart` and `OAI.Lech.ReesRoot.raise` (definitions bundle `OAIQ032L007` of this split); `OAI.Lech.finiteHomologyEuler` (definitions bundle `OAIQ032L013` of this split); `OAI.Lech.TorsionLength.DirectSumZero` (definitions bundle `OAIQ032L017` of this split); `OAI.Lech.ReesRoot.exceptionalZ` and `OAI.Lech.ReesRoot.quotientAt` (definitions bundle `OAIQ032L035` of this split).
--
--   **Used by.** The proof of `OAI.Lech.ReesRoot.sum_estimate` of this split imports it.
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
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ MonoidalCategory
open ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ)

variable (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))

variable [LinearOrder (Chart n)] (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p))

include hb hgen hds hmu ha B hflat in

lemma quotientAtTotal_euler (N : ℕ) (hN : h+n≤N) :
    finiteHomologyEuler ell ((quotientAt I z hz F h s hd m).total (.up ℤ)) (-(h:ℤ)) N=
      ∑ k∈Finset.range (h+1),(-1:ℝ)^k*(b (-(h:ℤ)+k):ℝ)*
        ∑ j∈Finset.range (IdealFiltered.order h s (-(h:ℤ)+k)),
          finiteHomologyEuler ell (exceptionalZ I z hz (raise m j)) 0 n := by
  sorry

end Lech.ReesRoot

end

end OAI
end
