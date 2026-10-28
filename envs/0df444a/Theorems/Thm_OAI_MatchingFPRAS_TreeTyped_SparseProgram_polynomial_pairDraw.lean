-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_TreeTyped_SparseProgram_polynomial_pairDraw
-- name    : OAI.MatchingFPRAS.TreeTyped.SparseProgram.polynomial_pairDraw
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:12:06.948946+00:00
-- url     : https://prove2.me/theorems/e95763ba-18b0-4937-bb90-88345620e0d9
-- title:
--   OAI.MatchingFPRAS.TreeTyped.SparseProgram.polynomial_pairDraw (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.TreeTyped.SparseProgram.polynomial_pairDraw` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Sampling/TreePairStep.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Sampling/TreePairStep.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.TreeTyped.SparseProgram`, with `open TreeTyped ExecutableOptions TreeFraction`):
--
--   ```lean
--   lemma polynomial_pairDraw {p : C×(E×V)→Bool} {q : C×(E×E)→Bool} {r : C×(E×(V×V))→Bool}
--       {t : C×(E×E)→Bool} {w z : C×E→Fraction}
--       {P : Realizer p} {Q : Realizer q} {R : Realizer r} {T : Realizer t} {W : Realizer w} {Z : Realizer z}
--       {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
--       {Le : Realizer (fun x : E×E=>decide (x.1≤x.2))}
--       {EqV : Realizer (fun x : V×V=>decide (x.1=x.2))}
--       {LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))}
--       (hP : PolynomialTime P) (hQ : PolynomialTime Q) (hR : PolynomialTime R) (hT : PolynomialTime T)
--       (hW : PolynomialTime W) (hZ : PolynomialTime Z)
--       (hE : PolynomialTime Eq) (hL : PolynomialTime Le) (hV : PolynomialTime EqV) (hlV : PolynomialTime LeV) :
--       PolynomialTime (pairDrawRealizer P Q R T W Z Eq Le EqV LeV)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.TreeFraction.Fraction`, `OAI.MatchingFPRAS.TreeTyped.Codec`, `OAI.MatchingFPRAS.TreeTyped.Realizer`, `OAI.MatchingFPRAS.TreeTyped.instCodecBool`, `OAI.MatchingFPRAS.TreeTyped.instCodecList`, `OAI.MatchingFPRAS.TreeTyped.instCodecNat` and `OAI.MatchingFPRAS.TreeTyped.instCodecProd` (definitions bundle `OAIQ051M000` of this split); `OAI.MatchingFPRAS.TreeTyped.SparseProgram.PairInput` and `OAI.MatchingFPRAS.TreeTyped.SparseProgram.PairState` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.TreeTyped.finsetCodec`, `OAI.MatchingFPRAS.TreeTyped.SparseProgram.pairDraw` and `OAI.MatchingFPRAS.TreeTyped.SparseProgram.pairDrawRealizer` (definitions bundle `OAIQ051M002` of this split); `OAI.MatchingFPRAS.TreeTyped.PolynomialTime` (definitions bundle `OAIQ051M004` of this split).
--
--   **Used by.** The proof of `OAI.MatchingFPRAS.NumericLadder.polynomial_pair` of this split imports it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Sampling/TreePairStep.lean (declaration OAI.MatchingFPRAS.TreeTyped.SparseProgram.polynomial_pairDraw)

import Mathlib
import Definitions.Def_OAIQ051M004

section

attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped ExecutableOptions TreeFraction

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

lemma polynomial_pairDraw {p : C×(E×V)→Bool} {q : C×(E×E)→Bool} {r : C×(E×(V×V))→Bool}
    {t : C×(E×E)→Bool} {w z : C×E→Fraction}
    {P : Realizer p} {Q : Realizer q} {R : Realizer r} {T : Realizer t} {W : Realizer w} {Z : Realizer z}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    {Le : Realizer (fun x : E×E=>decide (x.1≤x.2))}
    {EqV : Realizer (fun x : V×V=>decide (x.1=x.2))}
    {LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hQ : PolynomialTime Q) (hR : PolynomialTime R) (hT : PolynomialTime T)
    (hW : PolynomialTime W) (hZ : PolynomialTime Z)
    (hE : PolynomialTime Eq) (hL : PolynomialTime Le) (hV : PolynomialTime EqV) (hlV : PolynomialTime LeV) :
    PolynomialTime (pairDrawRealizer P Q R T W Z Eq Le EqV LeV) := by
  sorry

attribute [local instance] Transport.Sparse.pmOrder
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
end
