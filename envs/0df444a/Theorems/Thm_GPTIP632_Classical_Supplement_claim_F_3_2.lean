-- Prove2me | Theorems.Thm_GPTIP632_Classical_Supplement_claim_F_3_2
-- name    : GPTIP632.Classical.Supplement.claim_F_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:19:43.873596+00:00
-- url     : https://prove2.me/theorems/728bb952-4eae-44ab-8f6f-c29bad4a0c90
-- title:
--   Theorem F.3, Claim 2 — The acceptance probability of a quantum verifier against a prover strategy of G is a fixed linear functional, determined by V_x, evaluated on the
-- statement:
--   The source result is:
--
--   Claim 2: the acceptance probability depends only on $S$. […] Hence the acceptance probability is a fixed linear functional, determined by $V_x$,
--   evaluated on $S$.
--
--   For every theory G containing quantum theory, every quantum verifier V and input x, there is a real-linear functional ℓ_{V_x} on linear maps ⊗_i V_{M_i} → ⊗_i V_{M'_i} such that for every prover strategy P of G against V_x, Pr[V_x ↔ P accepts] = ℓ_{V_x}(S_P). The functional depends on V_x only, not on P or its private systems.
--
--   The concrete systems, gates, class definitions and any conclusion predicates are defined by the supplement interfaces. Completeness is at least 2/3 and soundness is at most 1/3, except for the explicitly quantified 0 < s < c < 1 clause of Lemma F.9. Every fixed message bound means at most k messages, counting both directions. No simulation theorem or class equality is assumed.
--
--   Differences from the source:
--   - generalization: theories closed under all sequential and parallel compositions → the published Theory interface requires channel-channel and instrument-instrument closure, without mixed closure axioms; reason: every source theory qualifies; the induced-map and circuit-value assertions use the actual positive unit-preserving maps and do not need mixed allowed-operation closure
--   - encoding: finite-dimensional systems, composites and quantum channels in fixed bases → real coordinate frames, binary-tree register presentations (including a labelled copy of Delta_3), Kraus gate matrices and complete positivity on every ancilla dimension; reason: these represent the same quantum, classical and transported cones; labels and parentheses carry no operational data
--   - encoding: the explicitly defined QC, classical and triangular theories are valid theories → existential proofs of PreTheory.Ok package the fixed concrete data into the published Theory type; reason: validity is a conclusion, not an added hypothesis; proof irrelevance makes all such proof witnesses describe exactly the same theory
--   - encoding: a fixed linear functional of the finite-dimensional comb determined by V_x → a real-linear functional on raw response kernels, chosen before the prover; reason: the finite contraction extends to all raw kernels by ignoring coordinates outside the message registers
--   - encoding: adaptive quantum or classical circuits in the source gate sets → published VData circuits and interaction probabilities, with zero-based outcome labels and classical copy as a constant-size circuit macro; reason: wire placements, total completion on malformed records, and recording the decision last preserve every physical interaction; copy is implemented using fixed preparation and reversible classical gates
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.29 (PDF p.31), Theorem F.3, Claim 2

import Mathlib
import Definitions.Def_GPTIP632_Classical_Supplement_Claims

set_option autoImplicit false

namespace GPTIP632.Classical.Supplement
open QAlgorithms.Complexity KTUnitary.Synth

theorem claim_F_3_2 :
    ∃ hQ : (qcPre []).Ok,
      ∀ (G : Theory), G.Standing → ∀ (E : QEmb G) (V : VData (qc0 hQ)),
        V.IsVerifier → QubitMsgs V → ∀ x : Str,
          ∃ F : (List G.C.Wire → List G.C.Wire → ℝ) →ₗ[ℝ] ℝ,
            ∀ P : Prover (E.push V) x,
              (E.push V).accProb x P = F (comb P ((E.push V).R x)) := by sorry

end GPTIP632.Classical.Supplement
