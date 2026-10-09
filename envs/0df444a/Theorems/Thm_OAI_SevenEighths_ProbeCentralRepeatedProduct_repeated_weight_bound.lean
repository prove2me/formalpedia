-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeCentralRepeatedProduct_repeated_weight_bound
-- name    : OAI.SevenEighths.ProbeCentralRepeatedProduct.repeated_weight_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:27:38.22913+00:00
-- url     : https://prove2.me/theorems/cbf105b7-2c7b-4657-9b39-f6069dd527fb
-- title:
--   Bound for a weighted central repeated term
-- statement:
--   Let $\eta$ be a `Character`, $u$ a `FreeRow`, $P$ a `Supported` prime ideal coprime to $\eta.\mathrm{modulus}$ with $N(P)\ge480$ and `repeatedRowPrime u P`, reals $a\in[51/100,1]$, $0<e\le1/1000$ with $198N(P)^{-10e}\le1/2$, $B\ge0$, $Y$, $W$ bounded by $B$, and $x,w,z\in\mathbb C$ with $\operatorname{Re}x=a+16e$, $\operatorname{Re}w=1-a-6e$, $\operatorname{Re}z=17/50$. Then
--   $$\|W(N(P)/Y)\,N(P)^{z-1}\,\texttt{centralRepeatedTerm}\,\eta\,u\,P\,x\,w\,z\|\le812\,B\,N(P)^{\operatorname{Re}z}N(P)^{-\operatorname{Re}w}.$$
--
--   Lean: `OAI.SevenEighths.ProbeCentralRepeatedProduct.repeated_weight_bound` in `lean/OAI/NumberTheory/DirichletL/Detector/CentralRepeatedProduct.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B023

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedProduct
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CompletedGauss
open HeckeDeletionBounds HeckeReciprocalGrowth
local notation "O" => HeckeFamily.O

lemma repeated_weight_bound (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hη : IsCoprime P.val η.modulus)
    (a e B Y : ℝ) (W : ℝ→ℂ) (x w z : ℂ)
    (hB : 0≤B) (hW : ∀t,‖W t‖≤B)
    (hQ : (480:ℝ)≤P.val.absNorm) (hsmall : 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hr : repeatedRowPrime u P) :
    ‖W ((P.val.absNorm:ℝ)/Y)*(P.val.absNorm:ℂ)^(z-1)*centralRepeatedTerm η u P hs x w z‖≤
      (812*B*(P.val.absNorm:ℝ)^z.re)*(P.val.absNorm:ℝ)^(-w.re) := by
  sorry

end SevenEighths.ProbeCentralRepeatedProduct

end

end OAI
end
