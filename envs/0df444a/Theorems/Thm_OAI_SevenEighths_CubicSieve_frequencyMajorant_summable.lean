-- Prove2me | Theorems.Thm_OAI_SevenEighths_CubicSieve_frequencyMajorant_summable
-- name    : OAI.SevenEighths.CubicSieve.frequencyMajorant_summable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T22:54:40.743985+00:00
-- url     : https://prove2.me/theorems/a603a62e-0316-41a8-97c2-9b598971d0df
-- title:
--   The frequency majorant is summable
-- statement:
--   For all reals $M>0$ and $N\ge1$, the sequence `frequencyMajorant M N : ℕ → ℝ` is summable.
--
--   Lean: `OAI.SevenEighths.CubicSieve.frequencyMajorant_summable` in `lean/OAI/NumberTheory/DirichletL/CubicSieve/Majorant.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B008

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

theorem frequencyMajorant_summable (M N : ℝ) (hM : 0 < M) (hN : 1 ≤ N) :
    Summable (frequencyMajorant M N) := by
  sorry

end
end SevenEighths.CubicSieve

end OAI
end
