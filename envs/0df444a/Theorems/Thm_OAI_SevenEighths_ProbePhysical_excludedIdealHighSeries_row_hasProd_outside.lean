-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_excludedIdealHighSeries_row_hasProd_outside
-- name    : OAI.SevenEighths.ProbePhysical.excludedIdealHighSeries_row_hasProd_outside
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:23:23.111763+00:00
-- url     : https://prove2.me/theorems/975ec208-6fde-46b0-b097-32dfa644db00
-- title:
--   Euler product over primes outside S for the high row series
-- statement:
--   For the same data, the product over prime ideals outside $S$ of `idealRowHighLocalFactor η u P x w z` converges to `markedIdealHighSeries S 1 η u x w z`.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.excludedIdealHighSeries_row_hasProd_outside` in `lean/OAI/NumberTheory/DirichletL/Detector/HighRowsLocal.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

theorem excludedIdealHighSeries_row_hasProd_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>idealRowHighLocalFactor η u P.val.val x w z)
      (markedIdealHighSeries S 1 η u x w z) := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
