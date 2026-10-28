-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_normalized_fejer_entry
-- name    : OAI.Kadison.FreeBlocks.normalized_fejer_entry
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:48:46.256054+00:00
-- url     : https://prove2.me/theorems/090f7739-c52b-494e-9cdd-5a1b4c1ca2e2
-- title:
--   OAI.Kadison.FreeBlocks.normalized_fejer_entry: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open UniformSpace`, `open scoped ComplexOrder InnerProductSpace`, `open FreeMoments FreeWordTensor DihedralCorner`):
--
--   ```lean
--   lemma normalized_fejer_entry (e0 : D) (e : Corner hp)
--       (heq : f e0=(e:A)) (heproj : IsStarProjection e)
--       (he : e∈cornerFactor hp (S false) hpD)
--       (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖)
--       (N : ℕ) (hN : 0 < N) (i j : Fin N) :
--       ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=Completion (factorSpace t S true)) (F:=t.functional.GNS)
--         (normalizedColumn t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr i.val).toContinuousLinearMap).comp
--         (t.functional.gnsStarAlgHom ((e:A)*((fejerCorner hp (d*s) (2*N):Corner hp):A)*(e:A)))).comp
--         (normalizedColumn t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr j.val).toContinuousLinearMap =
--       ((halfCornerTrace hp t.functional.toLinearMap e).re:ℂ) •
--         ((2*t.functional (wave (d*s) ((i.val:ℤ)-j.val)*
--           ((fejerCorner hp (d*s) (2*N):Corner hp):A))) •
--             (1:Completion (factorSpace t S true) →L[ℂ] Completion (factorSpace t S true))+
--          (Complex.ofReal (((2*N:ℝ)-i.val-j.val-1)/(2*N:ℝ)^2)) • baseAction t S hfree (s:A))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.TracialGNS.algebraVector` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.Corner`, `OAI.Kadison.cornerSubalgebra`, `OAI.Kadison.instAlgebraComplexCorner`, `OAI.Kadison.instModuleComplexCorner`, `OAI.Kadison.instRingCorner`, `OAI.Kadison.instStarModuleComplexCorner` and `OAI.Kadison.instStarRingCorner` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.DihedralCorner.wave` (definitions bundle `OAIQ039C005` of this split); `OAI.Kadison.FreeMoments.Free`, `OAI.Kadison.FreeWordTensor.FaithfulState`, `OAI.Kadison.FreeWordTensor.faithfulNormed`, `OAI.Kadison.FreeWordTensor.preSpace` and `OAI.Kadison.FreeWordTensor.Space` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.FreeBlocks.factorSpace` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FreeBlocks.letterOf`, `OAI.Kadison.FreeBlocks.multiplicityLevel`, `OAI.Kadison.FreeBlocks.multiplicityTensor` and `OAI.Kadison.FreeBlocks.pullbackState` (definitions bundle `OAIQ039C036` of this split); `OAI.Kadison.FreeBlocks.factorTrace` (definitions bundle `OAIQ039C046` of this split); `OAI.Kadison.halfCornerTrace` (definitions bundle `OAIQ039C054` of this split); `OAI.Kadison.FreeBlocks.baseAction` (definitions bundle `OAIQ039C055` of this split); `OAI.Kadison.cornerFactor`, `OAI.Kadison.DihedralCorner.fejerCorner` and `OAI.Kadison.FreeBlocks.norm_letterOf_unitary` (definitions bundle `OAIQ039C059` of this split); `OAI.Kadison.FreeBlocks.normalizedColumn` (definitions bundle `OAIQ039C066` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.free_hankel_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C066

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

include htr hd hs hd0 hs0 hrot hd2 hs2 hpform hpd hdp hpD in
lemma normalized_fejer_entry (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e)
    (he : e∈cornerFactor hp (S false) hpD)
    (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖)
    (N : ℕ) (hN : 0 < N) (i j : Fin N) :
    ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=Completion (factorSpace t S true)) (F:=t.functional.GNS)
      (normalizedColumn t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr i.val).toContinuousLinearMap).comp
      (t.functional.gnsStarAlgHom ((e:A)*((fejerCorner hp (d*s) (2*N):Corner hp):A)*(e:A)))).comp
      (normalizedColumn t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr j.val).toContinuousLinearMap =
    ((halfCornerTrace hp t.functional.toLinearMap e).re:ℂ) •
      ((2*t.functional (wave (d*s) ((i.val:ℤ)-j.val)*
        ((fejerCorner hp (d*s) (2*N):Corner hp):A))) •
          (1:Completion (factorSpace t S true) →L[ℂ] Completion (factorSpace t S true))+
       (Complex.ofReal (((2*N:ℝ)-i.val-j.val-1)/(2*N:ℝ)^2)) • baseAction t S hfree (s:A)) := by
  sorry

end Kadison.FreeBlocks

end

end
end

end OAI
end
