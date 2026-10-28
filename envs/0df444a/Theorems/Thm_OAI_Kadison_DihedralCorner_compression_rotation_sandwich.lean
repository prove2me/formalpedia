-- Prove2me | Theorems.Thm_OAI_Kadison_DihedralCorner_compression_rotation_sandwich
-- name    : OAI.Kadison.DihedralCorner.compression_rotation_sandwich
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:33:35.843677+00:00
-- url     : https://prove2.me/theorems/f70ff46b-21a0-40f8-912f-9b9cb13807a8
-- title:
--   OAI.Kadison.DihedralCorner.compression_rotation_sandwich: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.DihedralCorner`, with `open FreeMoments`):
--
--   ```lean
--   lemma compression_rotation_sandwich (hpD : p∈S i) (e b : Corner hp)
--       (he : e∈cornerFactor hp (S i) hpD)
--       (hb : b∈cosineAlgebra (d*s) d hr hp hpform hdp)
--       (hb0 : halfCornerTrace hp τ b=0) (a c : ℤ) :
--       τ (wave (d*s) a*((e:A)*(b:A)*(e:A))*wave (d*s) (-c))=
--         (halfCornerTrace hp τ e)^2*τ (wave (d*s) (a-c)*(b:A))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.Corner`, `OAI.Kadison.cornerSubalgebra`, `OAI.Kadison.instAlgebraComplexCorner`, `OAI.Kadison.instModuleComplexCorner`, `OAI.Kadison.instRingCorner`, `OAI.Kadison.instStarModuleComplexCorner` and `OAI.Kadison.instStarRingCorner` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.DihedralCorner.wave` (definitions bundle `OAIQ039C005` of this split); `OAI.Kadison.FreeMoments.Free` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.halfCornerTrace` and `OAI.Kadison.DihedralCorner.cosineAlgebra` (definitions bundle `OAIQ039C054` of this split); `OAI.Kadison.cornerFactor` (definitions bundle `OAIQ039C059` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.dihedral_entry_pairing` of this split imports it.
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

namespace Kadison.DihedralCorner

open FreeMoments

variable {A : Type*} [CStarAlgebra A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} (τ : A →ₗ[ℂ] ℂ)

variable (h1 : τ 1=1) (htr : ∀ a b : A, τ (a*b)=τ (b*a))
  (hstar : ∀ a : A, τ (star a)=star (τ a)) (hfree : Free S τ)

variable (d s : unitary A) (i j : ι) (hij : i≠j)

variable (hd : (d : A)∈S i) (hs : (s : A)∈S j)
  (hd0 : τ (d : A)=0) (hs0 : τ (s : A)=0)

variable (hr : MulAut.conj d (d*s)=(d*s)⁻¹) (hd2 : (d : A)*(d : A)=1)

variable {p : A} (hp : IsStarProjection p) (hpform : p=(1/2 : ℂ) • (1+(d : A)))
  (hpd : p*(d : A)=p) (hdp : (d : A)*p=p)

include h1 htr hstar hfree hij hd hs hd0 hs0 hd2 hpd in
lemma compression_rotation_sandwich (hpD : p∈S i) (e b : Corner hp)
    (he : e∈cornerFactor hp (S i) hpD)
    (hb : b∈cosineAlgebra (d*s) d hr hp hpform hdp)
    (hb0 : halfCornerTrace hp τ b=0) (a c : ℤ) :
    τ (wave (d*s) a*((e:A)*(b:A)*(e:A))*wave (d*s) (-c))=
      (halfCornerTrace hp τ e)^2*τ (wave (d*s) (a-c)*(b:A)) := by
  sorry

end Kadison.DihedralCorner

end

end
end

end OAI
end
