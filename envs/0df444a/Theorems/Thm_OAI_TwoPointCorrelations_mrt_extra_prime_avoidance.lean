-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_extra_prime_avoidance
-- name    : OAI.TwoPointCorrelations.mrt_extra_prime_avoidance
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:21.994074+00:00
-- url     : https://prove2.me/theorems/bfa5cd2e-fb34-4071-810b-dda5873d8d36
-- title:
--   Few integers in a long interval avoid the extra prime band (e^{2L^{79/80}}, e^{L/log L}]
-- statement:
--   There is $C>0$ such that for all sufficiently large $L$ and all naturals $A$ and $N\ne0$ with $N\ge e^L$,
--
--   $$\frac1N\#\Big\{0\le j<N:\ \text{no prime }p\text{ with }e^{2L^{79/80}}<p\le e^{L/\log L}\text{ divides }A+j\Big\}\le\frac{C\log L}{L^{1/80}},$$
--
--   the band being `mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)`, and the proportion the probability under the uniform law on $\{0,\dots,N-1\}$ (`uniformFiniteLaw`).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_extra_prime_avoidance`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Filter
open Finset

theorem mrt_extra_prime_avoidance : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ (A N : ℕ) [NeZero N], Real.exp L ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun j => mrtPrimeAvoids
          (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) (A+j.val)) ≤
        C*Real.log L/L^(1/80:ℝ) := by
  sorry

end OAI.TwoPointCorrelations
