-- Prove2me | Theorems.Thm_OptStochMatch_Tight_upper_bound_cgpv
-- name    : OptStochMatch.Tight.upper_bound_cgpv
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:55:34.69109+00:00
-- url     : https://prove2.me/theorems/eb647a30-1f39-47b9-9bf4-432e9ae60f6b
-- title:
--   Upper bound of [7] — Chierichetti–Giacchini–Panconesi–Vattani: CR ≤ 1 − e/e^e and CRiid ≤ 1 − e/e^e
-- statement:
--   $\mathrm{CR}\le1-e/e^e$ and $\mathrm{CR}_{\mathrm{iid}}\le1-e/e^e$. This is the upper bound of Chierichetti, Giacchini, Panconesi and Vattani [7] (ICALP 2025, 58:1–58:20), which the paper cites and does not prove (p. 1; proof of Theorem 5.5, p. 26).
--
--   Differences from the source:
--   - encoding: online policies: decisions from the current arrival, the history and independent internal randomization → PoissonPolicy / IIDPolicy: one Uniform[0,1] seed and a decision map measurable in the seed and arrival times; reason: a single uniform seed generates any independent internal randomness; past decisions are functions of the seed and past arrivals; same policy class
--   - encoding: CR and CRiid as inf over instances with OPT > 0 of sup over algorithms knowing the instance → real sInf over instances (m, λ) resp. (n ≥ 1, m, µ with ∑µ = 1) with OPT > 0 of real sSup of ALG/OPT over policies of that instance; reason: the inner sets are nonempty and bounded (ALG ≤ m), the outer set is nonempty and bounded below by 0, so sInf/sSup are the source's inf/sup
--   - encoding: Poisson processes of intensities λ_S on [0,1] → Janossy densities e^{−∑λ_S} ∏ λ_{s_k} on ordered arrival times; reason: the law of the superposition of independent type-wise Poisson processes; same law
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), p. 1 (PDF p. 2) and proof of Theorem 5.5, p. 26 (PDF p. 27), citing [7] Chierichetti, Giacchini, Panconesi, Vattani, ICALP 2025, 58:1–58:20

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Matching

namespace OptStochMatch.Tight

/-- The upper bound of Chierichetti, Giacchini, Panconesi and Vattani [7] (ICALP 2025), as cited
on p. 1 (PDF 2) and in the proof of Theorem 5.5 (p. 26, PDF 27):
`CR ≤ 1 − e/e^e` and `CRiid ≤ 1 − e/e^e`. -/
theorem upper_bound_cgpv : CR ≤ cStar ∧ CRiid ≤ cStar := by sorry

end OptStochMatch.Tight
