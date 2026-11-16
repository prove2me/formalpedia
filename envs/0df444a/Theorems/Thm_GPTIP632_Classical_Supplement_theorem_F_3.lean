-- Prove2me | Theorems.Thm_GPTIP632_Classical_Supplement_theorem_F_3
-- name    : GPTIP632.Classical.Supplement.theorem_F_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:21:08.900014+00:00
-- url     : https://prove2.me/theorems/3a8a01a9-f819-4c4b-8668-b0ab7e776aee
-- title:
--   Theorem F.3 — For a theory G containing quantum theory, every quantum verifier has the same value against provers of G as against quantum provers; consequently
-- statement:
--   The source result is:
--
--   Theorem F.3 (Quantum verifiers). Let $\mathcal G$ be a theory containing quantum theory. For every
--   quantum verifier $V$ and every input $x$,
--   $$\mathrm{val}_{\mathcal G}(V_x) = \mathrm{val}_{\mathrm{quantum}}(V_x),$$
--   the value over quantum provers. Consequently $\mathsf{GIP}_{\mathrm{qm}}(\mathcal G; k) = \mathsf{QIP}(k)$ for every $k$, and $\mathsf{GIP}_{\mathrm{qm}}(\mathcal G) =
--   \mathsf{GIP}_{\mathrm{qm}}(\mathcal G; 3) = \mathsf{QIP} = \mathsf{PSPACE}$.
--
--   All clauses, as a conjunction: (a) value equality for every quantum verifier V and every input x; (b) GIP_qm(G; k) = QIP(k) for every k ∈ ℕ; (c) GIP_qm(G) = GIP_qm(G; 3); (d) GIP_qm(G; 3) = QIP; (e) QIP = KTUnitary.Synth.PromisePSPACE at the empty oracle. Hypotheses: G a published GPTIP632.Classical.Theory that contains quantum theory (Definition D.4 (i)–(iii)); G.Standing may be assumed (the paper imposes (T1)–(T4) on every theory, p.17) but nothing else. QIP = QIP(3) = PSPACE (Fact A.5) is NOT a hypothesis.
--
--   The concrete systems, gates, class definitions and any conclusion predicates are defined by the supplement interfaces. Completeness is at least 2/3 and soundness is at most 1/3, except for the explicitly quantified 0 < s < c < 1 clause of Lemma F.9. Every fixed message bound means at most k messages, counting both directions. No simulation theorem or class equality is assumed.
--
--   Differences from the source:
--   - generalization: theories closed under all sequential and parallel compositions → the published Theory interface requires channel-channel and instrument-instrument closure, without mixed closure axioms; reason: every source theory qualifies; the induced-map and circuit-value assertions use the actual positive unit-preserving maps and do not need mixed allowed-operation closure
--   - encoding: finite-dimensional systems, composites and quantum channels in fixed bases → real coordinate frames, binary-tree register presentations (including a labelled copy of Delta_3), Kraus gate matrices and complete positivity on every ancilla dimension; reason: these represent the same quantum, classical and transported cones; labels and parentheses carry no operational data
--   - encoding: the explicitly defined QC, classical and triangular theories are valid theories → existential proofs of PreTheory.Ok package the fixed concrete data into the published Theory type; reason: validity is a conclusion, not an added hypothesis; proof irrelevance makes all such proof witnesses describe exactly the same theory
--   - encoding: quantum verifiers for G and quantum provers for the same circuit → a QC verifier pushed along a quantum embedding; quantum value uses only finite-dimensional quantum memories in QC; reason: QIP is defined independently of G; the statement also concludes that the pushed circuit is a verifier
--   - encoding: adaptive quantum or classical circuits in the source gate sets → published VData circuits and interaction probabilities, with zero-based outcome labels and classical copy as a constant-size circuit macro; reason: wire placements, total completion on malformed records, and recording the decision last preserve every physical interaction; copy is implemented using fixed preparation and reversible classical gates
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.28 (PDF p.30), Theorem F.3

import Mathlib
import Definitions.Def_GPTIP632_Classical_Supplement_Claims

set_option autoImplicit false

namespace GPTIP632.Classical.Supplement
open QAlgorithms.Complexity KTUnitary.Synth

theorem theorem_F_3 :
    ∃ hQ : (qcPre []).Ok,
      (qc0 hQ).Standing ∧
      ∀ (G : Theory), G.Standing → ∀ E : QEmb G,
        (∀ V : VData (qc0 hQ), V.IsVerifier → QubitMsgs V →
          (E.push V).IsVerifier ∧ ∀ x : Str, (E.push V).val x = valQ V x) ∧
        (∀ k : ℕ, GIPqmk G E hQ k = QIPk hQ k) ∧
        GIPqm G E hQ = GIPqmk G E hQ 3 ∧
        GIPqmk G E hQ 3 = QIP hQ ∧ QIP hQ = PromisePSPACE O₀ := by sorry

end GPTIP632.Classical.Supplement
