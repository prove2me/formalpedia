-- Prove2me | Theorems.Thm_OAI_Lech_ReesRoot_unfilteredTotal_finite
-- name    : OAI.Lech.ReesRoot.unfilteredTotal_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:42:53.609577+00:00
-- url     : https://prove2.me/theorems/10b15c3d-cc0e-461b-92b5-ba27dd09a69c
-- title:
--   OAI.Lech.ReesRoot.unfilteredTotal_finite: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.ReesRoot`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ MonoidalCategory`):
--
--   ```lean
--   lemma unfilteredTotal_finite (i : ℤ) :
--       ell.finiteClass (((TensorTotal.Right.functor F).obj (cechZ I z hz m)).homology i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.TorsionLength` (definitions bundle `OAIQ032L000` of this split); `OAI.Lech.TensorTotal.Right.functor` (definitions bundle `OAIQ032L002` of this split); `OAI.Lech.ProductSourceCover.Chart` (definitions bundle `OAIQ032L007` of this split); `OAI.Lech.baseChangeFunctor` and `OAI.Lech.baseChangeFunctor_additive` (definitions bundle `OAIQ032L008` of this split); `OAI.Lech.TorsionLength.DirectSumZero` and `OAI.Lech.TorsionLength.finiteClass` (definitions bundle `OAIQ032L017` of this split); `OAI.Lech.ReesRoot.cechZ` (definitions bundle `OAIQ032L035` of this split).
--
--   **Used by.** The proofs of `OAI.Lech.ReesRoot.ambient_euler_additive`, `OAI.Lech.ReesRoot.unfilteredEuler_affine_step`, `OAI.Lech.ReesRoot.unfilteredEuler_diagonal` and `OAI.Lech.ReesRoot.unfilteredEuler_rank` of this split import it.
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
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ) (m : Fin n → ℤ)

variable [LinearOrder (ProductSourceCover.Chart n)]
  (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p)) (hp : ∀ p,Module.Projective R (F.X p))
  (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)

include hgen hds hmu ha B hflat hp hfin hb hac in

lemma unfilteredTotal_finite (i : ℤ) :
    ell.finiteClass (((TensorTotal.Right.functor F).obj (cechZ I z hz m)).homology i) := by
  sorry
end Lech.ReesRoot

end

end OAI
end
