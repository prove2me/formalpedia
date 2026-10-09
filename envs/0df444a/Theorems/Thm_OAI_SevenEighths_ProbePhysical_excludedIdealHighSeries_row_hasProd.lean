-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_excludedIdealHighSeries_row_hasProd
-- name    : OAI.SevenEighths.ProbePhysical.excludedIdealHighSeries_row_hasProd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:28:10.266886+00:00
-- url     : https://prove2.me/theorems/23889d95-b77e-46c1-aa8c-a7aade04c63e
-- title:
--   Euler product for the excluded high row series
-- statement:
--   For a finite set $S$ of prime ideals, $\eta$, $u$ and $x,w,z$ with $\operatorname{Re}x>3/2$, $\operatorname{Re}w>2$, $\operatorname{Re}z>1/6$, the product over prime ideals of $\sum_b$`markedIdealHighSummand S 1 η u x w z (P^…)…` converges to `markedIdealHighSeries S 1 η u x w z`.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.excludedIdealHighSeries_row_hasProd` in `lean/OAI/NumberTheory/DirichletL/Detector/HighRowsExcluded.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem excludedIdealHighSeries_row_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      markedIdealHighSummand S 1 η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (markedIdealHighSeries S 1 η u x w z) := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
