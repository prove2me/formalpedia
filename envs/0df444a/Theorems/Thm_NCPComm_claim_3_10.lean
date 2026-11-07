-- Prove2me | Theorems.Thm_NCPComm_claim_3_10
-- name    : NCPComm.claim_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:05:02.952203+00:00
-- url     : https://prove2.me/theorems/d528b9a5-edc3-4628-870d-65470fc9cc5c
-- title:
--   Claim 3.10 — sequential amplification
-- statement:
--   If an interactive proof has both errors at most $\varepsilon<\frac12$, then for odd $t$, its $t$ sequential repetitions with fresh samples and coins and a majority verdict have both errors at most
--   $$
--   \exp\big(-2t(\tfrac12-\varepsilon)^2\big).
--   $$
--   Sample, communication and round bounds increase by at most a factor $t$. Moreover, $t$ independent Poisson sample pools of mean $s$ have total size distributed as $\mathrm{Poi}(ts)$.
--
--   **Formalization Note** The conclusion asserts the existence of a protocol $Q$ in the model with these parameters, for an arbitrary promise problem $(\mathrm{Yes},\mathrm{No})$.
--
--   Differences from the source:
--   - encoding: the repetition protocol, with fresh samples and coins and a majority verdict → a protocol Q with Poisson mean t·s, depth ≤ t·depth and rounds ≤ t·rounds with the stated errors; reason: in the model of a pool held up front, the repetition splits one pool of mean t·s into t independent pools; only the parameters and errors enter the later statements
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Claim 3.10, p.16

import Mathlib
import Definitions.Def_NCPComm_IPProtocol

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Claim 3.10 (Sequential amplification), p.16** (Herman, The Communication Complexity of
Verifying Distribution Properties, STOC 2027 submission, manuscript sha256 714c0353…).

If `P` has both errors at most `ε < 1/2` for a promise problem, then for odd `t` there is a protocol
`Q` (the `t` sequential repetitions with fresh samples and coins and a majority verdict) with both
errors at most `exp(-2t(1/2-ε)²)`, Poisson mean `t·s`, communication at most `t` times that of `P`
and rounds at most `t` times those of `P`. Moreover `t` independent Poisson pools of mean `s` have
total size distributed as `Poi(ts)`.

**Formalization Note** The conclusion is existential over the protocol model. In this model the
amplified verifier splits its pool of mean `t·s` into `t` independent pools of mean `s` by assigning
each sample to a uniform repetition. -/
theorem claim_3_10 {N : ℕ} (P : IPProtocol N) (s : ℝ≥0) (Yes No : Set (PMF (Fin N))) (ε : ℝ)
    (hε : ε < 1 / 2) (t : ℕ) (ht : Odd t) (hP : IsProofFor P s Yes No ε) :
    (∃ Q : IPProtocol N, Q.depth ≤ t * P.depth ∧ Q.rounds ≤ t * P.rounds ∧
      IsProofFor Q ((t : ℝ≥0) * s) Yes No (Real.exp (-2 * (t : ℝ) * (1 / 2 - ε) ^ 2))) ∧
    poolTotal s t = poissonLaw ((t : ℝ≥0) * s) := by sorry

end NCPComm
