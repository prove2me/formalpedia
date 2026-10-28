-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_propagation_from_corner
-- name    : OAI.Kadison.FreeBlocks.propagation_from_corner
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:37:41.523209+00:00
-- url     : https://prove2.me/theorems/e4246fe9-058c-4848-b826-8df6cbe2dd18
-- title:
--   OAI.Kadison.FreeBlocks.propagation_from_corner: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open scoped InnerProductSpace ComplexOrder`, `open Filter Topology ContinuousLinearMap`, `open FreeWordTensor FreeMoments`):
--
--   ```lean
--   theorem propagation_from_corner {κ : Type*} [Fintype κ] [DecidableEq κ]
--       (s : letterSpace t S j) (hs : ‖s‖=1)
--       (q : D) (hq : IsStarProjection q)
--       (w : κ → D)
--       (hcol : ∀ i j, star (w i)*w j=if i=j then q else 0)
--       (hinit : ∀ i, q*star (w i)=star (w i))
--       (htotal : ∑ i, w i*star (w i)=1)
--       (c : ℝ) (hc : 0 ≤ c)
--       (x : ℕ → letterSpace t S i) (hx : ∀ n, ‖x n‖=1)
--       (hxq : ∀ n, letterValue t S i (x n)*f q=letterValue t S i (x n))
--       (hxx : ∀ n, star (letterValue t S i (x n))*letterValue t S i (x n)=(c:ℂ) • f q)
--       (hxs : ∀ n, ‖t.functional.toPreGNS (star (letterValue t S i (x n)))‖≤1)
--       (hmoment : ∀ a ∈ S i, Tendsto (fun n => t.functional (letterValue t S i (x n)*a)) atTop (𝓝 0))
--       (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
--         Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))
--       (k : ℕ) (R : ℝ)
--       (hR : ∀ n, ‖(letterValue t S j s*letterValue t S i (x n))^k*letterValue t S j s‖≤R)
--       (ε : ℝ) (hε : 0≤ε)
--       (hsmall : ∀ a : t.functional.GNS →L[ℂ] t.functional.GNS, a∈M →
--         t.functional.gnsStarAlgHom (f q)*a=a → a*t.functional.gnsStarAlgHom (f q)=a →
--           ‖G.comp a-a.comp G‖≤ε*‖a‖)
--       (v : multiplicityLevel t S j 0) :
--       ‖B (k+1) (repeatInsertion t S s hs (k+1) v)-
--         repeatInsertion t S s hs (k+1) (B 0 v)‖≤32*ε*‖v‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FreeMoments.Free`, `OAI.Kadison.FreeWordTensor.FaithfulState`, `OAI.Kadison.FreeWordTensor.faithfulNormed`, `OAI.Kadison.FreeWordTensor.letterSpace`, `OAI.Kadison.FreeWordTensor.letterValue`, `OAI.Kadison.FreeWordTensor.preSpace` and `OAI.Kadison.FreeWordTensor.Space` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.FreeBlocks.factorSpace` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FreeBlocks.multiplicityLevel`, `OAI.Kadison.FreeBlocks.multiplicityTensor` and `OAI.Kadison.FreeWordTensor.generatedOperators` (definitions bundle `OAIQ039C036` of this split); `OAI.Kadison.FreeBlocks.repeatInsertion` (definitions bundle `OAIQ039C055` of this split); `OAI.Kadison.FreeBlocks.repeatedOutput` (definitions bundle `OAIQ039C059` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.propagation_from_stage_all` of this split imports it.
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

open scoped InnerProductSpace ComplexOrder

open Filter Topology ContinuousLinearMap

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι} (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (B : ∀ n, multiplicityLevel t S j n →L[ℂ] multiplicityLevel t S j n)

variable (hB : ∀ n d (x : letterSpace t S i) v,
  G (repeatedOutput t S f hf hS hfree hij d x n v)=
    repeatedOutput t S f hf hS hfree hij d x n (B n v))

variable (hGL : ∀ d : D, G.comp (t.functional.gnsStarAlgHom (f d))=
  (t.functional.gnsStarAlgHom (f d)).comp G)

variable (M : VonNeumannAlgebra t.functional.GNS)
  (hM : ∀ a : A, t.functional.gnsStarAlgHom a∈M)

include hB hGL hM in
theorem propagation_from_corner {κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : letterSpace t S j) (hs : ‖s‖=1)
    (q : D) (hq : IsStarProjection q)
    (w : κ → D)
    (hcol : ∀ i j, star (w i)*w j=if i=j then q else 0)
    (hinit : ∀ i, q*star (w i)=star (w i))
    (htotal : ∑ i, w i*star (w i)=1)
    (c : ℝ) (hc : 0 ≤ c)
    (x : ℕ → letterSpace t S i) (hx : ∀ n, ‖x n‖=1)
    (hxq : ∀ n, letterValue t S i (x n)*f q=letterValue t S i (x n))
    (hxx : ∀ n, star (letterValue t S i (x n))*letterValue t S i (x n)=(c:ℂ) • f q)
    (hxs : ∀ n, ‖t.functional.toPreGNS (star (letterValue t S i (x n)))‖≤1)
    (hmoment : ∀ a ∈ S i, Tendsto (fun n => t.functional (letterValue t S i (x n)*a)) atTop (𝓝 0))
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))
    (k : ℕ) (R : ℝ)
    (hR : ∀ n, ‖(letterValue t S j s*letterValue t S i (x n))^k*letterValue t S j s‖≤R)
    (ε : ℝ) (hε : 0≤ε)
    (hsmall : ∀ a : t.functional.GNS →L[ℂ] t.functional.GNS, a∈M →
      t.functional.gnsStarAlgHom (f q)*a=a → a*t.functional.gnsStarAlgHom (f q)=a →
        ‖G.comp a-a.comp G‖≤ε*‖a‖)
    (v : multiplicityLevel t S j 0) :
    ‖B (k+1) (repeatInsertion t S s hs (k+1) v)-
      repeatInsertion t S s hs (k+1) (B 0 v)‖≤32*ε*‖v‖ := by
  sorry

end Kadison.FreeBlocks

end

end
end

end OAI
end
