-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_small_original_physical_tail
-- name    : OAI.SevenEighths.ProbeHighRowFamily.small_original_physical_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:28:59.002004+00:00
-- url     : https://prove2.me/theorems/c0167226-13ad-4e3e-9630-ebca515b2399
-- title:
--   Small-row physical tail bound
-- statement:
--   For $K$, $0<e<1/1000$, $0<\delta\le1/2$, $a,b>0$, $B\ge0$, $\beta\ge7/8$, $S$ maximal with `SourceExclusions S` and `FirstTail (1/4) S`, Schwartz $W_0,W_1$ as above, there is $C>0$ such that for every $\eta$, $Z\ge1$, finite set $F$ of dyadic indices with $2^n\le Z^{1/100}$, row sets $R_n$ of rows $u\ne1$ with $2^n\le N((u))\le2^{n+1}$, slot data, lengths summing to $1/6$ and weights: $\sum_{n\in F}\|\texttt{finitePhysicalRows}(\dots,R_n,\dots)\|\le C\,N(\eta.\mathrm{modulus})^{\delta}Z^{\beta-11/16-63/800+8e}$.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.small_original_physical_tail` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/PhysicalSmallTail.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem small_original_physical_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤Z^(1/100:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      (∑n∈F,‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := by
  sorry

end SevenEighths.ProbeHighRowFamily
end

end OAI
end
