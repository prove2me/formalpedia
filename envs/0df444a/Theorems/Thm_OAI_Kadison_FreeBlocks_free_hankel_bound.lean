-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_free_hankel_bound
-- name    : OAI.Kadison.FreeBlocks.free_hankel_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:36:33.221751+00:00
-- url     : https://prove2.me/theorems/fbff9911-2924-4b03-9a4a-55ea323904ed
-- title:
--   OAI.Kadison.FreeBlocks.free_hankel_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open UniformSpace`, `open scoped ComplexOrder InnerProductSpace`, `open FreeMoments FreeWordTensor DihedralCorner`):
--
--   ```lean
--   theorem free_hankel_bound (e0 : D) (e : Corner hp)
--       (heq : f e0=(e:A)) (heproj : IsStarProjection e)
--       (he : e∈cornerFactor hp (S false) hpD)
--       (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖)
--       (c ε : ℝ) (hc : 0 ≤ c) (hε : 0≤ε)
--       (hsmall : ∀ a : A, (e:A)*a*(e:A)=a →
--         ‖G*t.functional.gnsStarAlgHom a-t.functional.gnsStarAlgHom a*G‖≤ε*‖a‖)
--       (hprop : ∀ n v, ‖B n (repeatInsertion t S sl sn n v)-
--         repeatInsertion t S sl sn n (B 0 v)‖≤(2*c*ε)*‖v‖)
--       (hprop' : ∀ n v,
--         ‖(ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true n)
--           (F:=multiplicityLevel t S true n) (B n)) (repeatInsertion t S sl sn n v)-
--         repeatInsertion t S sl sn n
--           ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true 0)
--             (F:=multiplicityLevel t S true 0) (B 0)) v)‖≤(2*c*ε)*‖v‖) :
--       ‖B 0*baseAction t S hfree (s:A)-baseAction t S hfree (s:A)*B 0‖≤16*(1+4*c)*ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.TracialGNS.algebraVector` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.Corner`, `OAI.Kadison.cornerSubalgebra`, `OAI.Kadison.instAlgebraComplexCorner`, `OAI.Kadison.instRingCorner`, `OAI.Kadison.instStarModuleComplexCorner` and `OAI.Kadison.instStarRingCorner` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.FreeMoments.Free`, `OAI.Kadison.FreeWordTensor.FaithfulState`, `OAI.Kadison.FreeWordTensor.faithfulNormed`, `OAI.Kadison.FreeWordTensor.letterSpace`, `OAI.Kadison.FreeWordTensor.preSpace` and `OAI.Kadison.FreeWordTensor.Space` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.FreeBlocks.factorSpace` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FreeBlocks.letterOf`, `OAI.Kadison.FreeBlocks.multiplicityLevel`, `OAI.Kadison.FreeBlocks.multiplicityTensor` and `OAI.Kadison.FreeBlocks.pullbackState` (definitions bundle `OAIQ039C036` of this split); `OAI.Kadison.FreeBlocks.factorTrace` (definitions bundle `OAIQ039C046` of this split); `OAI.Kadison.FreeBlocks.baseAction` and `OAI.Kadison.FreeBlocks.repeatInsertion` (definitions bundle `OAIQ039C055` of this split); `OAI.Kadison.cornerFactor`, `OAI.Kadison.FreeBlocks.norm_letterOf_unitary` and `OAI.Kadison.FreeBlocks.repeatedOutput` (definitions bundle `OAIQ039C059` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.stage_hankel_bound` of this split imports it.
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

open scoped ComplexOrder InnerProductSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S false=f.range)

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hrot : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)
local notation "sl" => (letterOf t S true (s:A) hs hs0)
local notation "sn" => (norm_letterOf_unitary t S true s hs hs0)
local notation "dl" => (letterOf t S false (d:A) hd hd0)
local notation "dn" => (norm_letterOf_unitary t S false d hd hd0)

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (B : ∀ n, multiplicityLevel t S true n →L[ℂ] multiplicityLevel t S true n)

variable (hB : ∀ n a (x : letterSpace t S false) v,
  G (repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n v)=
    repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n (B n v))

variable (hB' : ∀ n a (x : letterSpace t S false) v,
  G.adjoint (repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n v)=
    repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n
      ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true n)
        (F:=multiplicityLevel t S true n) (B n)) v))

include htr hd hs hd0 hs0 hrot hd2 hs2 hpform hpd hdp hpD hB hB' in
theorem free_hankel_bound (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e)
    (he : e∈cornerFactor hp (S false) hpD)
    (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖)
    (c ε : ℝ) (hc : 0 ≤ c) (hε : 0≤ε)
    (hsmall : ∀ a : A, (e:A)*a*(e:A)=a →
      ‖G*t.functional.gnsStarAlgHom a-t.functional.gnsStarAlgHom a*G‖≤ε*‖a‖)
    (hprop : ∀ n v, ‖B n (repeatInsertion t S sl sn n v)-
      repeatInsertion t S sl sn n (B 0 v)‖≤(2*c*ε)*‖v‖)
    (hprop' : ∀ n v,
      ‖(ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true n)
        (F:=multiplicityLevel t S true n) (B n)) (repeatInsertion t S sl sn n v)-
      repeatInsertion t S sl sn n
        ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true 0)
          (F:=multiplicityLevel t S true 0) (B 0)) v)‖≤(2*c*ε)*‖v‖) :
    ‖B 0*baseAction t S hfree (s:A)-baseAction t S hfree (s:A)*B 0‖≤16*(1+4*c)*ε := by
  sorry

end Kadison.FreeBlocks

end

end
end

end OAI
end
