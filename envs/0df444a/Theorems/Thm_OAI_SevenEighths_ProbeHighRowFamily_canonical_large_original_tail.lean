-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_canonical_large_original_tail
-- name    : OAI.SevenEighths.ProbeHighRowFamily.canonical_large_original_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:20:09.017095+00:00
-- url     : https://prove2.me/theorems/f3b6f419-b18d-45b9-85ec-6263013275be
-- title:
--   Large-row physical tail is negligible
-- statement:
--   For $K$, $0<\delta\le1$, $\zeta>0$, $a,b>0$, $B\ge0$, `saving`, $S$ maximal with `SourceExclusions S` and `FirstTail (1/4) S`, and Schwartz $W_0,W_1$ supported in $[a_0,b_0]$, $[a_1,b_1]$ ($a_0,a_1>0$), there is $C>0$ such that for every $\eta$, $Z\ge1$, slot sets outside $S$ with injective tuples, lengths $\ge0$ summing to $1/6$, and weights supported in $[a,b]$ bounded by $B$: the dyadic row blocks `finitePhysicalRows … (dyadicRows (Z^{13/16+ζ}) n) …` are summable and the sum of their norms is at most $C\,N(\eta.\mathrm{modulus})^{\delta}Z^{-\mathrm{saving}}$.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.canonical_large_original_tail` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/CanonicalTails.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

theorem canonical_large_original_tail (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>finitePhysicalRows S hmax η (dyadicRows (Z^((13/16:ℝ)+ζ)) n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z) ∧
      (∑'n,‖finitePhysicalRows S hmax η (dyadicRows (Z^((13/16:ℝ)+ζ)) n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  sorry

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
