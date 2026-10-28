-- Prove2me | Theorems.Thm_OAI_Lech_ReesRoot_sum_estimate
-- name    : OAI.Lech.ReesRoot.sum_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:26:06.730839+00:00
-- url     : https://prove2.me/theorems/7cca7820-f1dd-485f-b1ea-ef30bedca95b
-- title:
--   OAI.Lech.ReesRoot.sum_estimate: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.ReesRoot`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover FiniteModuleCech`):
--
--   ```lean
--   theorem sum_estimate (r : Fin n → ℤ) (hr : RootPositions n s r) :
--       0≤(n.factorial:ℝ)*ell.realValue (F.homology 0)+
--         ell.realValue (ModuleCat.of R (R ⧸ I))*
--           ∑ i∈Finset.range (n+2),(-1:ℝ)^i*(b (-(i:ℤ)):ℝ)*rootStripPolynomial n r i s
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.TorsionLength` (definitions bundle `OAIQ032L000` of this split); `OAI.Lech.ProductSourceCover.Chart`, `OAI.Lech.ProductSourceCover.RootPositions` and `OAI.Lech.ProductSourceCover.rootStripPolynomial` (definitions bundle `OAIQ032L007` of this split); `OAI.Lech.baseChangeFunctor` and `OAI.Lech.baseChangeFunctor_additive` (definitions bundle `OAIQ032L008` of this split); `OAI.Lech.TorsionLength.realValue` (definitions bundle `OAIQ032L013` of this split); `OAI.Lech.Koszul.unit` (definitions bundle `OAIQ032L014` of this split); `OAI.Lech.TorsionLength.DirectSumZero` (definitions bundle `OAIQ032L017` of this split).
--
--   **Used by.** The proof of `OAI.Lech.complex_estimate_allModule` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L007
import Definitions.Def_OAIQ032L013
import Definitions.Def_OAIQ032L014
import Definitions.Def_OAIQ032L017

section

attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover FiniteModuleCech
universe u
variable {R : Type u} [CommRing R] [Nontrivial R] (I : Ideal R) {n : ℕ}
  [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (hK : ∀ a : ℕ,1≤a → ∀ i : ℤ,i<0 →
    ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (s : ℕ)
  (hd : ∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hf : ∀ p,Module.Free R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)
  (hbr : ∑ k∈Finset.range (n+2),(-1:ℝ)^k*(b (-(n+1:ℤ)+k):ℝ)=0)

include hz hgen hds hmu ha hK hd B hf hfin hb hac hbr in

theorem sum_estimate (r : Fin n → ℤ) (hr : RootPositions n s r) :
    0≤(n.factorial:ℝ)*ell.realValue (F.homology 0)+
      ell.realValue (ModuleCat.of R (R ⧸ I))*
        ∑ i∈Finset.range (n+2),(-1:ℝ)^i*(b (-(i:ℤ)):ℝ)*rootStripPolynomial n r i s := by
  sorry
end Lech.ReesRoot

end

end OAI
end
