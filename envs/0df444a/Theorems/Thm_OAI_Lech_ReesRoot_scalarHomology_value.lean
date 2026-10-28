-- Prove2me | Theorems.Thm_OAI_Lech_ReesRoot_scalarHomology_value
-- name    : OAI.Lech.ReesRoot.scalarHomology_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:53:58.386177+00:00
-- url     : https://prove2.me/theorems/4d22c6c7-50e0-4c58-9523-02babe8c42ba
-- title:
--   OAI.Lech.ReesRoot.scalarHomology_value: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.ReesRoot`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex FiniteModuleCech MonoidalCategory`):
--
--   ```lean
--   theorem scalarHomology_value (i : ℤ) :
--       ell.value ((tensorCech F (scalarCechDiagram I z hz)).homology i)=ell.value (F.homology i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.TorsionLength` (definitions bundle `OAIQ032L000` of this split); `OAI.Lech.baseChangeFunctor` and `OAI.Lech.baseChangeFunctor_additive` (definitions bundle `OAIQ032L008` of this split); `OAI.Lech.Koszul.unit` (definitions bundle `OAIQ032L014` of this split); `OAI.Lech.TorsionLength.DirectSumZero` (definitions bundle `OAIQ032L017` of this split); `OAI.Lech.FiniteModuleCech.tensorCech` (definitions bundle `OAIQ032L024` of this split); `OAI.Lech.ReesRoot.scalarCechDiagram` (definitions bundle `OAIQ032L026` of this split).
--
--   **Used by.** The proof of `OAI.Lech.ReesRoot.scalarEuler_value` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L017
import Definitions.Def_OAIQ032L024
import Definitions.Def_OAIQ032L026

section

attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex FiniteModuleCech MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)

variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

variable [Nontrivial R] (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (hK : ∀ a : ℕ,1≤a → ∀ i : ℤ,i<0 →
    ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
  (hf : ∀ p,Module.Free R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)

include hgen hds hmu ha hK hf hfin hb hac in
theorem scalarHomology_value (i : ℤ) :
    ell.value ((tensorCech F (scalarCechDiagram I z hz)).homology i)=ell.value (F.homology i) := by
  sorry

end Lech.ReesRoot

end

end OAI
end
