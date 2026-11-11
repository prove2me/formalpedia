-- Prove2me | Theorems.Thm_GPTIP632_Classical_fact_A_2
-- name    : GPTIP632.Classical.fact_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:30.140231+00:00
-- url     : https://prove2.me/theorems/53edb3d1-c775-4d00-bb4b-d02ca86fb7a2
-- title:
--   Fact A.2: IP = PSPACE, with public-coin systems of perfect completeness and soundness $1/3$
-- statement:
--   This is the classical theorem of Lund, Fortnow, Karloff and Nisan, Shamir, and Shen, cited by the paper as Fact A.2.
--
--   As classes of promise problems,
--
--   $$
--   \mathsf{IP}=\mathsf{PSPACE}.
--   $$
--
--   Moreover, every promise problem $L$ in $\mathsf{PSPACE}$ has an interactive proof system in which the verifier's messages are uniformly random strings (a public-coin system), with perfect completeness and soundness $1/3$ against arbitrary randomised provers:
--
--   1. for every $x\in L_{\rm yes}$ some prover makes the verifier accept with probability $1$;
--   2. for every $x\in L_{\rm no}$ every randomised prover makes it accept with probability at most $1/3$.
--
--   It is the lower-bound ingredient of Theorem E.5, where these verifiers are implemented with the classical gates of an arbitrary theory.
--
--   Differences from the source:
--   - encoding: a (deterministic) polynomial-time Turing machine → a deterministic oracle Turing machine (QAdvFew.PoQOracle.OTM) run with the empty oracle for p(|input|) steps, its output read off the work tape; reason: a clocked machine is a polynomial-time machine and conversely
--   - encoding: PSPACE, as a class of promise problems → KTUnitary.Synth.PromisePSPACE at the empty oracle: an OTM halting on every input within space p(|x|) (input cells counted) and answering correctly on L_yes ∪ L_no; reason: the standard machine definition; counting the input cells changes nothing for polynomial space
--   - encoding: a verifier that exchanges polynomially many messages of polynomial length with the prover → R(n) rounds, each an ℓ(n)-bit verifier message followed by an ℓ(n)-bit prover reply, R and ℓ polynomials; the decision is computed from (x, coins, transcript); reason: padding; a protocol in which the prover speaks first uses a dummy first message
--   - encoding: a prover is an arbitrary, possibly randomised, function from the conversation so far to the next message → a prover is a family of conditional distributions of its next message given the conversation so far; reason: a randomised prover with memory induces such conditionals, and every such family is a randomised prover
--   - reading: a public-coin system: the verifier's messages are uniformly random strings → coins = R·ℓ and the message of round j is the j-th ℓ-bit block of the coins, on every input; reason: the standard meaning of public coin; reading it with additional private coins would weaken the existence claim
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.12 (PDF p.14), Fact A.2 and Definition A.1

import Mathlib
import Definitions.Def_GPTIP632_Classical_IP
import Definitions.Def_KTUnitary_Synth_PromisePSPACE

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace GPTIP632.Classical

/-- **Fact A.2 (Lund–Fortnow–Karloff–Nisan; Shamir; Shen)**, p.12: `IP = PSPACE` as classes of promise
problems; and every promise problem in PSPACE has a public-coin interactive proof system with
perfect completeness and soundness `1/3` against arbitrary randomised provers. -/
theorem fact_A_2 :
    IP = KTUnitary.Synth.PromisePSPACE O₀ ∧
    ∀ L ∈ KTUnitary.Synth.PromisePSPACE O₀, ∃ V : IPVerifier, V.PublicCoin ∧ ∀ x : Str,
      (x ∈ L.1 → ∃ π, V.IsProver x π ∧ V.acc x π = 1) ∧
      (x ∈ L.2 → ∀ π, V.IsProver x π → V.acc x π ≤ 1 / 3) := by sorry

end GPTIP632.Classical
