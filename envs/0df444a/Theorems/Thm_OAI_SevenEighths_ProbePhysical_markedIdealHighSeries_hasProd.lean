-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_markedIdealHighSeries_hasProd
-- name    : OAI.SevenEighths.ProbePhysical.markedIdealHighSeries_hasProd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:20:36.261267+00:00
-- url     : https://prove2.me/theorems/89397297-502f-480a-b6b9-cda0f426ae6a
-- title:
--   Euler product for the marked high series
-- statement:
--   For a finite set $S$ of prime ideals, a finite set $T$ of prime ideals, $\eta$ and $x,w,z$ with $\operatorname{Re}x>3/2$, $\operatorname{Re}w>2$, $\operatorname{Re}z>1/6$: the product over prime ideals $P$ of $\sum_b$`markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b` converges (`HasProd`) to `markedIdealHighSeries S (∏_{P∈T} P) η 1 x w z`.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.markedIdealHighSeries_hasProd` in `lean/OAI/NumberTheory/DirichletL/Detector/MarkedEuler.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEulerFinsupp
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem markedIdealHighSeries_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b)
      (markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z) := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
