-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeEuler_pow_mul_sqrt
-- name    : OAI.SevenEighths.ProbeEuler.pow_mul_sqrt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T20:33:40.089264+00:00
-- url     : https://prove2.me/theorems/f9bbb8e1-fe68-4f01-b2c2-5474e4e9f4b2
-- title:
--   A power times a square root is a half-integer real power
-- statement:
--   For every real $Q>0$ and every natural number $n$, $Q^n\sqrt{Q}=Q^{\,n+1/2}$, the right side being the real power `Real.rpow`.
--
--   Lean: `OAI.SevenEighths.ProbeEuler.pow_mul_sqrt` in `lean/OAI/NumberTheory/DirichletL/Detector/HighRowsFirstTerms.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeEuler

lemma pow_mul_sqrt (Q : ℝ) (hQ : 0<Q) (n : ℕ) : Q^n*Real.sqrt Q=Q^((n:ℝ)+1/2) := by
  sorry

end SevenEighths.ProbeEuler
end

end OAI
end
