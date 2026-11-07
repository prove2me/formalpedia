-- Prove2me | Theorems.Thm_NCPComm_claim_3_9
-- name    : NCPComm.claim_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:02:43.911893+00:00
-- url     : https://prove2.me/theorems/36971105-2ad7-42c8-bded-f4c7cde278e2
-- title:
--   Claim 3.9 — sample reconstruction and interaction
-- statement:
--   **Reconstruction.** An independent sample represented by its counts is recovered in distribution by taking each label as many times as it occurs and ordering the resulting multiset uniformly. This preserves the joint law with the prover's initial information, provided that information and the sample are independent conditional on $D$.
--
--   **Interaction.** If two joint laws of the prover's retained information and the verifier's multiplicity indicators are within $\eta$ in total variation, then applying the same strategies to them changes the law of (transcript, verdict) by at most $\eta$, provided the strategies use only their retained information, the exchanged messages and fresh independent coins. In particular the acceptance probabilities differ by at most $\eta$.
--
--   This is what lets Alice and Bob run the protocol from a setup rather than from the distribution itself.
--
--   Differences from the source:
--   - encoding: multiplicity indicators (v_i)_i → the count function on labels, with v_i(x) = 1 iff the count at x is i; reason: the two determine each other, and s′ is the total of the counts
--   - encoding: an independent sample, given D and the prover's independent information → a prior ρ on a parameter γ, with D = dist γ, sample size law size γ and information law info γ; reason: the conditional independence is written as a bind; fixed and Poissonized sizes are the instances
--   - encoding: "for any fixed cheating-prover strategy" → any prover strategy of the retained information; reason: a fixed strategy is a constant one
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Claim 3.9, p.16

import Mathlib
import Definitions.Def_NCPComm_IPProtocol

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Claim 3.9 (Sample reconstruction and interaction), p.16** (Herman, The Communication
Complexity of Verifying Distribution Properties, STOC 2027 submission, manuscript sha256 714c0353…).

First part: an independent sample represented by its counts is recovered in distribution by
uniformly ordering the multiset of the counts, jointly with the prover's initial information `i`,
which is independent of the sample conditional on `D`. The choice `γ` of the distribution `dist γ`
and of the size law `size γ` is arbitrary, which covers fixed sizes and Poissonized sizes.

Second part: if two joint laws of the prover's retained information and the verifier's counts are
within `η` in total variation, then the same strategies change the transcript-and-verdict law by at
most `η`, and the acceptance probabilities differ by at most `η`.

**Formalization Note** `interactionLaw` makes each strategy read only its own part of the joint law,
the transcript, and fresh coins. -/
theorem claim_3_9 {N : ℕ} :
    (∀ {Γ I : Type} (ρ : PMF Γ) (dist : Γ → PMF (Fin N)) (size : Γ → PMF ℕ) (info : Γ → PMF I),
      let J : PMF (I × List (Fin N)) := ρ.bind fun γ => (info γ).bind fun i =>
        ((size γ).bind (OAI.ThreeState.iidList (dist γ))).map fun l => (i, l)
      (J.bind fun il => (uniformOrder (countVec il.2)).map fun l' => (il.1, l')) = J) ∧
    (∀ {I : Type} (J₁ J₂ : PMF (I × (Fin N → ℕ))) (η : ℝ) (depth : ℕ)
        (speaker : Transcript → Bool) (prover : I → PMF ProverBehaviour)
        (verifier : (Fin N → ℕ) → PMF VerifierBehaviour),
      OAI.ThreeState.tvMass J₁ J₂ ≤ η →
      OAI.ThreeState.tvMass (interactionLaw depth speaker prover verifier J₁)
          (interactionLaw depth speaker prover verifier J₂) ≤ η ∧
      |(((interactionLaw depth speaker prover verifier J₁).map Prod.snd) true).toReal
        - (((interactionLaw depth speaker prover verifier J₂).map Prod.snd) true).toReal| ≤ η) := by sorry

end NCPComm
