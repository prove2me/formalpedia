-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_free_fejer_norm
-- name    : OAI.Kadison.FreeBlocks.free_fejer_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:35:35.282765+00:00
-- url     : https://prove2.me/theorems/5e6e0884-1cde-4d3b-91d8-10eb759be34d
-- title:
--   OAI.Kadison.FreeBlocks.free_fejer_norm: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open scoped ComplexOrder`, `open FreeMoments FreeWordTensor DihedralCorner`):
--
--   ```lean
--   theorem free_fejer_norm (e : Corner hp) (heproj : IsStarProjection e)
--       (he : e∈cornerFactor hp (S false) hpD) (m : ℕ) (hm : 0 < m) :
--       ‖(e:A)*((fejerCorner hp (d*s) m:Corner hp):A)*(e:A)‖≤
--         4*Real.sqrt 2*Real.sqrt (halfCornerTrace hp t.functional.toLinearMap e).re*
--           Real.sqrt ((m:ℝ)⁻¹)+2*(halfCornerTrace hp t.functional.toLinearMap e).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.Corner`, `OAI.Kadison.cornerSubalgebra`, `OAI.Kadison.instAlgebraComplexCorner`, `OAI.Kadison.instModuleComplexCorner`, `OAI.Kadison.instRingCorner`, `OAI.Kadison.instStarModuleComplexCorner` and `OAI.Kadison.instStarRingCorner` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.FreeMoments.Free` and `OAI.Kadison.FreeWordTensor.FaithfulState` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.halfCornerTrace` (definitions bundle `OAIQ039C054` of this split); `OAI.Kadison.cornerFactor` and `OAI.Kadison.DihedralCorner.fejerCorner` (definitions bundle `OAIQ039C059` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.free_hankel_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C059

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hr : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)

include hfree htr hd hs hd0 hs0 hr hd2 hpform hpd hdp in
theorem free_fejer_norm (e : Corner hp) (heproj : IsStarProjection e)
    (he : e∈cornerFactor hp (S false) hpD) (m : ℕ) (hm : 0 < m) :
    ‖(e:A)*((fejerCorner hp (d*s) m:Corner hp):A)*(e:A)‖≤
      4*Real.sqrt 2*Real.sqrt (halfCornerTrace hp t.functional.toLinearMap e).re*
        Real.sqrt ((m:ℝ)⁻¹)+2*(halfCornerTrace hp t.functional.toLinearMap e).re := by
  sorry

end Kadison.FreeBlocks

end

end
end

end OAI
end
