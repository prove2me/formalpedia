-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_large_physical_tail_arbitrary_saving
-- name    : OAI.SevenEighths.ProbeHighRowFamily.large_physical_tail_arbitrary_saving
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:36.733517+00:00
-- url     : https://prove2.me/theorems/2aa0d815-ace7-4573-9557-b0570962a9fb
-- title:
--   Large dyadic physical tails are negligible
-- statement:
--   For $K$, $0<\delta\le1$, $\zeta>0$, $a,b>0$, $B\ge0$, `saving`, $S$ maximal with `SourceExclusions S` and `FirstTail (1/4) S`, Schwartz $W_0,W_1$ as above, there are $r\ge17/50$ and $C>0$ such that for every $\eta$, $Z\ge1$, dyadic row sets $R_n$ (rows $u\ne1$ with $Z^{13/16+\zeta}2^n\le N((u))\le2Z^{13/16+\zeta}2^n$), slot data, lengths summing to $1/6$ and weights: the `absolutePhysicalDyadIntegral … (R n) … 2 2 r` are summable with sum at most $C\,N(\eta.\mathrm{modulus})^{\delta}Z^{-\mathrm{saving}}$.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.large_physical_tail_arbitrary_saving` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/LargeSaving.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

theorem large_physical_tail_arbitrary_saving (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃r C : ℝ,(17/50:ℝ)≤ r ∧ 0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((13/16:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r) ∧
      (∑'n,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  sorry

end SevenEighths.ProbeHighRowFamily
end

end OAI
end
