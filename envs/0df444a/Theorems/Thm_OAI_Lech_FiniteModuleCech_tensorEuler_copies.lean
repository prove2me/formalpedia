-- Prove2me | Theorems.Thm_OAI_Lech_FiniteModuleCech_tensorEuler_copies
-- name    : OAI.Lech.FiniteModuleCech.tensorEuler_copies
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:50:46.940073+00:00
-- url     : https://prove2.me/theorems/2059c584-4558-4bbc-b6dc-cba424db7fb9
-- title:
--   OAI.Lech.FiniteModuleCech.tensorEuler_copies: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.FiniteModuleCech`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex`):
--
--   ```lean
--   lemma tensorEuler_copies (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
--       (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
--       (hflat : ∀ p,Module.Flat R (F.X p))
--       {κ : Type} [Fintype κ] (k : κ)
--       (hC : ∀ q,ell.finiteClass ((tensorCech F (copiesDiagram D κ)).homology q)) :
--       tensorEuler ell F h (copiesDiagram D κ)=(Fintype.card κ:ℝ)*tensorEuler ell F h D
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.TorsionLength` (definitions bundle `OAIQ032L000` of this split); `OAI.Lech.FiniteModuleCech.Diagram` (definitions bundle `OAIQ032L002` of this split); `OAI.Lech.FiniteModuleCech.copiesDiagram` (definitions bundle `OAIQ032L013` of this split); `OAI.Lech.TorsionLength.finiteClass` (definitions bundle `OAIQ032L017` of this split); `OAI.Lech.FiniteModuleCech.tensorCech` and `OAI.Lech.FiniteModuleCech.tensorEuler` (definitions bundle `OAIQ032L024` of this split).
--
--   **Used by.** The proof of `OAI.Lech.ReesRoot.unfilteredEuler_rank` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L017
import Definitions.Def_OAIQ032L024

section

attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]
  (D : Diagram R ι)

variable {I : Ideal R} (ell : TorsionLength I)

lemma tensorEuler_copies (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
    (hflat : ∀ p,Module.Flat R (F.X p))
    {κ : Type} [Fintype κ] (k : κ)
    (hC : ∀ q,ell.finiteClass ((tensorCech F (copiesDiagram D κ)).homology q)) :
    tensorEuler ell F h (copiesDiagram D κ)=(Fintype.card κ:ℝ)*tensorEuler ell F h D := by
  sorry
end Lech.FiniteModuleCech

end

end OAI
end
