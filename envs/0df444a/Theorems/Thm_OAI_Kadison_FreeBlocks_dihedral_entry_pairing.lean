-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_dihedral_entry_pairing
-- name    : OAI.Kadison.FreeBlocks.dihedral_entry_pairing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:34:43.853772+00:00
-- url     : https://prove2.me/theorems/b5cc2efb-05db-47bc-af40-5aebfa8b9e0a
-- title:
--   OAI.Kadison.FreeBlocks.dihedral_entry_pairing: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open UniformSpace`, `open scoped InnerProductSpace ComplexOrder`, `open FreeMoments FreeWordTensor DihedralCorner`):
--
--   ```lean
--   theorem dihedral_entry_pairing (heproj : IsStarProjection e)
--       (c : ℝ) (n m : ℕ) (v z : factorSpace t S true) :
--       inner ℂ (dihedralColumn t S hfree (e:A) (d*s) c n (z : multiplicityLevel t S true 0))
--         (t.functional.gnsStarAlgHom ((e:A)*(b:A)*(e:A))
--           (dihedralColumn t S hfree (e:A) (d*s) c m (v : multiplicityLevel t S true 0)))=
--       ((c:ℂ)^2*(halfCornerTrace hp t.functional.toLinearMap e)^2)*
--         (t.functional (wave (d*s) ((n:ℤ)-m)*(b:A))*
--           inner ℂ (z : multiplicityLevel t S true 0) (v : multiplicityLevel t S true 0)+
--          t.functional (wave (d*s) ((n:ℤ)+m+1)*(b:A))*
--           inner ℂ (z : multiplicityLevel t S true 0)
--             (baseAction t S hfree (s:A) (v : multiplicityLevel t S true 0)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.Corner`, `OAI.Kadison.cornerSubalgebra`, `OAI.Kadison.instAlgebraComplexCorner`, `OAI.Kadison.instModuleComplexCorner`, `OAI.Kadison.instRingCorner`, `OAI.Kadison.instStarModuleComplexCorner` and `OAI.Kadison.instStarRingCorner` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.DihedralCorner.wave` (definitions bundle `OAIQ039C005` of this split); `OAI.Kadison.FreeMoments.Free`, `OAI.Kadison.FreeWordTensor.FaithfulState`, `OAI.Kadison.FreeWordTensor.faithfulNormed`, `OAI.Kadison.FreeWordTensor.preSpace` and `OAI.Kadison.FreeWordTensor.Space` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.FreeBlocks.factorSpace` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FreeBlocks.multiplicityLevel` and `OAI.Kadison.FreeBlocks.multiplicityTensor` (definitions bundle `OAIQ039C036` of this split); `OAI.Kadison.halfCornerTrace` and `OAI.Kadison.DihedralCorner.cosineAlgebra` (definitions bundle `OAIQ039C054` of this split); `OAI.Kadison.FreeBlocks.baseAction` and `OAI.Kadison.FreeBlocks.dihedralColumn` (definitions bundle `OAIQ039C055` of this split); `OAI.Kadison.cornerFactor` (definitions bundle `OAIQ039C059` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.finite_fejer_entry` of this split imports it.
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

open UniformSpace

open scoped InnerProductSpace ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hr : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)

variable (e b : Corner hp) (he : e∈cornerFactor hp (S false) hpD)
  (hb : b∈cosineAlgebra (d*s) d hr hp hpform hdp)
  (hb0 : halfCornerTrace hp t.functional.toLinearMap b=0)

include htr hd hs hd0 hs0 hd2 hs2 hpd he hb hb0 in
theorem dihedral_entry_pairing (heproj : IsStarProjection e)
    (c : ℝ) (n m : ℕ) (v z : factorSpace t S true) :
    inner ℂ (dihedralColumn t S hfree (e:A) (d*s) c n (z : multiplicityLevel t S true 0))
      (t.functional.gnsStarAlgHom ((e:A)*(b:A)*(e:A))
        (dihedralColumn t S hfree (e:A) (d*s) c m (v : multiplicityLevel t S true 0)))=
    ((c:ℂ)^2*(halfCornerTrace hp t.functional.toLinearMap e)^2)*
      (t.functional (wave (d*s) ((n:ℤ)-m)*(b:A))*
        inner ℂ (z : multiplicityLevel t S true 0) (v : multiplicityLevel t S true 0)+
       t.functional (wave (d*s) ((n:ℤ)+m+1)*(b:A))*
        inner ℂ (z : multiplicityLevel t S true 0)
          (baseAction t S hfree (s:A) (v : multiplicityLevel t S true 0))) := by
  sorry

end Kadison.FreeBlocks

end

end
end

end OAI
end
