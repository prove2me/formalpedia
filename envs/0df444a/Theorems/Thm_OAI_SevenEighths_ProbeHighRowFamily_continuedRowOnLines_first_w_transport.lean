-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_continuedRowOnLines_first_w_transport
-- name    : OAI.SevenEighths.ProbeHighRowFamily.continuedRowOnLines_first_w_transport
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:39.513909+00:00
-- url     : https://prove2.me/theorems/69c1c81d-5230-4bd9-8cfc-3b066a93f696
-- title:
--   Moving the w line of the continued row integral
-- statement:
--   For $-1/100\le l\le r$, $\xi\ge17/50$, $S$ maximal with `SourceExclusions S` and `FirstTail (1/4) S`, primes outside $S$, $\eta$, $u\ne1$, Schwartz $W_0,W_1$ supported in $[a_0,b_0]$, $[a_1,b_1]$ ($a_0,a_1>0$) and $X,Y,Z>0$: $\int$`continuedRowOnLines … 2 l ξ` $d\,$`heightMeasure` $=\int$`continuedRowOnLines … 2 r ξ` $d\,$`heightMeasure`.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.continuedRowOnLines_first_w_transport` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/FirstTransport.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem continuedRowOnLines_first_w_transport {K : ℕ}
    (l r ξ : ℝ) (hl : -(1/100:ℝ)≤l) (hlr : l≤ r) (hξ : (17/50:ℝ)≤ξ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 l ξ p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 r ξ p ∂heightMeasure := by
  sorry

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
