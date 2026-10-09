-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_calibratedHighCoefficient_eq_bare
-- name    : OAI.SevenEighths.ProbePhysical.calibratedHighCoefficient_eq_bare
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:20:22.645211+00:00
-- url     : https://prove2.me/theorems/530ded3e-867b-40d4-9499-45872bd273c9
-- title:
--   Calibrated high coefficients are calibrated bare coefficients
-- statement:
--   Let $S$ be a finite set of maximal ideals of the Eisenstein integers, $\eta$ a `HeckeFamily.Character`, $I$ an ideal with nonzero `primaryGenerator`, $A,s$ `Supported` elements with the calibration generator coprime to $As$, and $H\in\mathcal O$. Then `calibratedHighCoefficient (calibrationForSet S hS) η I hI A s _ H` $=\overline{r(H)}\cdot$`bareSourceCoefficient η I hI A s _ H`, where $r$ is `(calibrationForSet S hS).residueMonoid`.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.calibratedHighCoefficient_eq_bare` in `lean/OAI/NumberTheory/DirichletL/Detector/CoefficientDirect.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ProbeRow ProbePhase
local notation "O" => ActualEisensteinCubic.O

theorem calibratedHighCoefficient_eq_bare (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (η : HeckeFamily.Character) (I : Ideal O) (hI : primaryGenerator I≠0)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    calibratedHighCoefficient (calibrationForSet S hS) η I hI A s (supportedElement_ne_zero A hA) H=
      star ((calibrationForSet S hS).residueMonoid H)*
        bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) H := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
