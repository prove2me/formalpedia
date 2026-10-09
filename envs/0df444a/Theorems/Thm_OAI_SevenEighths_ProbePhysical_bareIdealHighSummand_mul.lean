-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_bareIdealHighSummand_mul
-- name    : OAI.SevenEighths.ProbePhysical.bareIdealHighSummand_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:20:04.23636+00:00
-- url     : https://prove2.me/theorems/3ea6e253-1424-44e1-a3a9-6871e1a5f8b8
-- title:
--   The bare high summand is multiplicative
-- statement:
--   For a `HeckeFamily.Character` $\eta$, $x,w,z$ and ideals $I,J,K,L,I',J',K',L'$ of the Eisenstein integers with $IJKL$ coprime to $I'J'K'L'$: `bareIdealHighSummand η 1 x w z (II') (JJ') (KK') (LL')` is the product of the two summands at $(I,J,K,L)$ and $(I',J',K',L')$.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.bareIdealHighSummand_mul` in `lean/OAI/NumberTheory/DirichletL/Detector/IdealMultiplicative.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem bareIdealHighSummand_mul (η : HeckeFamily.Character) (x w z : ℂ)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighSummand η 1 x w z (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighSummand η 1 x w z I J K L * bareIdealHighSummand η 1 x w z I' J' K' L' := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
