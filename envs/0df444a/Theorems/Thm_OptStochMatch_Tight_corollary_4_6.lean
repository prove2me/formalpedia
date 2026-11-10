-- Prove2me | Theorems.Thm_OptStochMatch_Tight_corollary_4_6
-- name    : OptStochMatch.Tight.corollary_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:55:28.233261+00:00
-- url     : https://prove2.me/theorems/d6b1f836-962d-4f0e-baba-fe07bb6f07e0
-- title:
--   Corollary 4.6 — Poisson matching: an online policy with ALG ≥ (1 − e^{1−e}) OPT
-- statement:
--   For every Poisson matching instance with known arrival intensities there is an online policy with $\mathrm{ALG}\ge(1-e^{1-e})\,\mathrm{OPT}$.
--
--   Differences from the source:
--   - encoding: online policies: decisions from the current arrival, the history and independent internal randomization → PoissonPolicy / IIDPolicy: one Uniform[0,1] seed and a decision map measurable in the seed and arrival times; reason: a single uniform seed generates any independent internal randomness; past decisions are functions of the seed and past arrivals; same policy class
--   - encoding: Poisson processes of intensities λ_S on [0,1] → Janossy densities e^{−∑λ_S} ∏ λ_{s_k} on ordered arrival times; reason: the law of the superposition of independent type-wise Poisson processes; same law
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Corollary 4.6, p. 18 (PDF p. 19)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Matching
open scoped NNReal

namespace OptStochMatch.Tight

/-- Corollary 4.6 (p. 18, PDF 19). For every Poisson matching instance with known arrival
intensities, there is an online policy with `ALG ≥ (1 − e^{1−e}) OPT`. -/
theorem corollary_4_6 (m : ℕ) (lam : Ty m → ℝ≥0) :
    ∃ π : PoissonPolicy m, cStar * optPoisModel lam ≤ algPois lam π := by sorry

end OptStochMatch.Tight
