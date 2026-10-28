-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_stage_hankel_bound
-- name    : OAI.Kadison.FreeBlocks.stage_hankel_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:38:53.831226+00:00
-- url     : https://prove2.me/theorems/b9540b5a-5f33-454b-aa92-0386469f94ce
-- title:
--   OAI.Kadison.FreeBlocks.stage_hankel_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open UniformSpace`, `open scoped InnerProductSpace ComplexOrder`, `open ContinuousLinearMap`, `open FreeWordTensor FreeMoments DihedralCorner`):
--
--   ```lean
--   theorem stage_hankel_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
--       (n : ℕ) (q : Matrix (I n) (I n) ℂ) (hq : IsStarProjection q)
--       (α : ℝ) (hα : 0<α) (hατ : factorTrace t f hf (φ n q)=(α:ℂ))
--       (w : κ → D)
--       (hcol : ∀ i j, star (w i)*w j=if i=j then φ n q else 0)
--       (hinit : ∀ i, φ n q*star (w i)=star (w i))
--       (htotal : ∑ i, w i*star (w i)=1)
--       (e0 : D) (e : Corner hp)
--       (heq : f e0=(e:A)) (heproj : IsStarProjection e)
--       (he : e∈cornerFactor hp (S false) hpD)
--       (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖)
--       (ε : ℝ) (hε : 0≤ε)
--       (hsmallq : ∀ a : t.functional.GNS →L[ℂ] t.functional.GNS, a∈M →
--         t.functional.gnsStarAlgHom (f (φ n q))*a=a →
--         a*t.functional.gnsStarAlgHom (f (φ n q))=a → ‖G.comp a-a.comp G‖≤ε*‖a‖)
--       (hsmalle : ∀ a : A, (e:A)*a*(e:A)=a →
--         ‖G*t.functional.gnsStarAlgHom a-t.functional.gnsStarAlgHom a*G‖≤ε*‖a‖) :
--       ‖(ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := multiplicityLevel t S true 0) (F := t.functional.GNS)
--         (baseEmbedding t S hfree).toContinuousLinearMap).comp
--         ((G*t.functional.gnsStarAlgHom (s:A)-t.functional.gnsStarAlgHom (s:A)*G).comp
--           (baseEmbedding t S hfree).toContinuousLinearMap)‖≤1040*ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.TracialGNS.algebraVector` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.Corner`, `OAI.Kadison.cornerSubalgebra`, `OAI.Kadison.instAlgebraComplexCorner`, `OAI.Kadison.instRingCorner`, `OAI.Kadison.instStarModuleComplexCorner` and `OAI.Kadison.instStarRingCorner` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.FreeMoments.Free`, `OAI.Kadison.FreeWordTensor.FaithfulState`, `OAI.Kadison.FreeWordTensor.faithfulNormed`, `OAI.Kadison.FreeWordTensor.preSpace` and `OAI.Kadison.FreeWordTensor.Space` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.TracialGNS.stageAlgebra` and `OAI.Kadison.TracialGNS.stageUnitary` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.FreeBlocks.factorSpace` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FreeBlocks.multiplicityLevel`, `OAI.Kadison.FreeBlocks.multiplicityTensor`, `OAI.Kadison.FreeBlocks.pullbackState` and `OAI.Kadison.FreeWordTensor.generatedOperators` (definitions bundle `OAIQ039C036` of this split); `OAI.Kadison.FreeBlocks.factorTrace` (definitions bundle `OAIQ039C046` of this split); `OAI.Kadison.FreeBlocks.baseEmbedding` (definitions bundle `OAIQ039C055` of this split); `OAI.Kadison.cornerFactor` and `OAI.Kadison.FreeBlocks.innerRepresentation` (definitions bundle `OAIQ039C059` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.normal_free_corner_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C059

section

attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

open ContinuousLinearMap

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments DihedralCorner

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (S : Bool → StarSubalgebra ℂ A)
  (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S false=f.range)
  (hfree : Free S t.functional.toLinearMap)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
  (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)
  (inc : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (hinc : ∀ n m (h : n ≤ m) a, φ m (inc h a)=φ n a)
  (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
  (hDgen : ∀ a : D, (factorTrace t f hf).gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer
      (TracialGNS.stageAlgebra (factorTrace t f hf) I φ : Set _)))

variable (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
  Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)
  (hGL : ∀ a : D, G.comp (t.functional.gnsStarAlgHom (f a))=
    (t.functional.gnsStarAlgHom (f a)).comp G)
  (hGW : ∀ n u, G.comp
    (innerRepresentation t htr f S false hS hfree hgen (TracialGNS.stageUnitary (φ n) u)).toLinearIsometry.toContinuousLinearMap =
    (innerRepresentation t htr f S false hS hfree hgen (TracialGNS.stageUnitary (φ n) u)).toLinearIsometry.toContinuousLinearMap.comp G)

variable (M : VonNeumannAlgebra t.functional.GNS) (hM : ∀ a : A, t.functional.gnsStarAlgHom a∈M)

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hrot : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)

include htr hinc hsize hDgen hgen hGL hGW hM hd hs hd0 hs0 hrot hd2 hs2 hpform hpd hdp hpD in
theorem stage_hankel_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (q : Matrix (I n) (I n) ℂ) (hq : IsStarProjection q)
    (α : ℝ) (hα : 0<α) (hατ : factorTrace t f hf (φ n q)=(α:ℂ))
    (w : κ → D)
    (hcol : ∀ i j, star (w i)*w j=if i=j then φ n q else 0)
    (hinit : ∀ i, φ n q*star (w i)=star (w i))
    (htotal : ∑ i, w i*star (w i)=1)
    (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e)
    (he : e∈cornerFactor hp (S false) hpD)
    (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖)
    (ε : ℝ) (hε : 0≤ε)
    (hsmallq : ∀ a : t.functional.GNS →L[ℂ] t.functional.GNS, a∈M →
      t.functional.gnsStarAlgHom (f (φ n q))*a=a →
      a*t.functional.gnsStarAlgHom (f (φ n q))=a → ‖G.comp a-a.comp G‖≤ε*‖a‖)
    (hsmalle : ∀ a : A, (e:A)*a*(e:A)=a →
      ‖G*t.functional.gnsStarAlgHom a-t.functional.gnsStarAlgHom a*G‖≤ε*‖a‖) :
    ‖(ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := multiplicityLevel t S true 0) (F := t.functional.GNS)
      (baseEmbedding t S hfree).toContinuousLinearMap).comp
      ((G*t.functional.gnsStarAlgHom (s:A)-t.functional.gnsStarAlgHom (s:A)*G).comp
        (baseEmbedding t S hfree).toContinuousLinearMap)‖≤1040*ε := by
  sorry

end Kadison.FreeBlocks

end

end
end

end OAI
end
