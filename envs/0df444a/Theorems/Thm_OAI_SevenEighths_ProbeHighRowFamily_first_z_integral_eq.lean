-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_first_z_integral_eq
-- name    : OAI.SevenEighths.ProbeHighRowFamily.first_z_integral_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:18:55.204883+00:00
-- url     : https://prove2.me/theorems/13deed6f-44b9-4471-84db-90e917d2ebed
-- title:
--   Moving the z line of the physical row kernel
-- statement:
--   For $\epsilon>0$, $S$ maximal with `SourceExclusions S` and `FirstTail (ε/2) S`, primes outside $S$, $\eta$, $u$, Schwartz $W_0$ supported in $[a,b]$ ($a>0$), $W_1$, $X,Z>0$, $Y$, $x,w$ with $\operatorname{Re}x\ge51/100$, $\operatorname{Re}w\ge-1/100$, $\operatorname{Re}x+\operatorname{Re}w\ge1+\epsilon$, and $17/50\le l\le r$: $\int\texttt{continuedPhysicalRowKernel}(\dots,x,w,l+it)\,dt=\int\texttt{continuedPhysicalRowKernel}(\dots,x,w,r+it)\,dt$.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.first_z_integral_eq` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/ZShift.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Complex Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem first_z_integral_eq {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W0⊆Icc a b)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w : ℂ) (l r : ℝ) (hlr : l≤ r)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re)
    (hxw : 1+eps≤x.re+w.re) (hl : (17/50:ℝ)≤l) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((l:ℂ)+t*I))=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((r:ℂ)+t*I) := by
  sorry

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
