-- Prove2me | Theorems.Thm_GPTIP632_Classical_Supplement_theorem_G_5
-- name    : GPTIP632.Classical.Supplement.theorem_G_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:25:21.874051+00:00
-- url     : https://prove2.me/theorems/6874e7e3-cd2a-465b-a283-57a39251d3a3
-- title:
--   Theorem G.5 — For v ∈ (0,1), G^Q_v satisfies (T1)–(T4), contains quantum and classical theory and is isomorphic to QC with Δ3 adjoined; GIP_cl = GIP_qm = PSPAC
-- statement:
--   The source result is:
--
--   Theorem G.5 (Quantum theory with a triangular system adjoined). Let $v \in (0, 1)$ and let $\mathcal G^{\mathrm Q}_v$ be
--   the theory of Example B.23.
--     (i) $\mathcal G^{\mathrm Q}_v$ satisfies (T1)–(T4), contains quantum theory in the sense of Definition D.4 and classical
--         theory in the sense of (T3), and is isomorphic as a theory to $\mathsf{QC}$ with $\Delta_3$ adjoined as an
--         elementary system.
--    (ii) $\mathsf{GIP}_{\mathrm{cl}}(\mathcal G^{\mathrm Q}_v) = \mathsf{GIP}_{\mathrm{qm}}(\mathcal G^{\mathrm Q}_v) = \mathsf{PSPACE}$; the quantum subtheory has $\mathsf{GIP} = \mathsf{QIP} = \mathsf{PSPACE}$, and
--         the classical subtheory has $\mathsf{GIP} = \mathsf{IP} = \mathsf{PSPACE}$.
--   (iii) $L_v \in \mathsf{GMA}(\mathcal G^{\mathrm Q}_v)$.
--    (iv) If $v$ is not computable, then $\mathsf{GIP}(\mathcal G^{\mathrm Q}_v)$ contains an undecidable promise problem, so $\mathsf{GIP}(\mathcal G^{\mathrm Q}_v) \supsetneq$
--         $\mathsf{PSPACE}$.
--
--   For every v ∈ (0,1), with G^Q_v the constructed Theory of Example B.23: (i) Standing ∧ ContainsQuantum ∧ (T3) ∧ an isomorphism of theories (p.18 definition) between G^Q_v and QC_[3]; (ii) GIPcl = PromisePSPACE O₀ ∧ GIPqm = PromisePSPACE O₀; QC (qubits and classical bits with the quantum and classical gates) is a subtheory of G^Q_v with gate set contained in its gate set, and GIP(QC) = QIP = PSPACE; classical theory (Example B.17) is a subtheory with gate set contained, and GIP(classical theory) = IP (published GPTIP632_Classical_IP) = PSPACE; (iii) L_v ∈ GMA(G^Q_v); (iv) if v is not computable, ∃ L ∈ GIP(G^Q_v) undecidable and PSPACE ⊂ GIP(G^Q_v) strictly. Every clause.
--
--   The concrete systems, gates, class definitions and any conclusion predicates are defined by the supplement interfaces. Completeness is at least 2/3 and soundness is at most 1/3, except for the explicitly quantified 0 < s < c < 1 clause of Lemma F.9. Every fixed message bound means at most k messages, counting both directions. No simulation theorem or class equality is assumed.
--
--   Differences from the source:
--   - encoding: finite-dimensional systems, composites and quantum channels in fixed bases → real coordinate frames, binary-tree register presentations (including a labelled copy of Delta_3), Kraus gate matrices and complete positivity on every ancilla dimension; reason: these represent the same quantum, classical and transported cones; labels and parentheses carry no operational data
--   - encoding: the explicitly defined QC, classical and triangular theories are valid theories → existential proofs of PreTheory.Ok package the fixed concrete data into the published Theory type; reason: validity is a conclusion, not an added hypothesis; proof irrelevance makes all such proof witnesses describe exactly the same theory
--   - encoding: quantum and classical subtheories, with their stated classes, and an isomorphism with QC with Delta_3 adjoined → subtheory maps on coordinates, operations and gates, and mutually inverse unit- and tensor-compatible theory matrices; the adjoined dimension is encoded by [2]; reason: system presentation aliases may coincide as physical systems; designated gates are preserved by the subtheory maps but are not required to be preserved by the operational isomorphism
--   - encoding: adaptive quantum or classical circuits in the source gate sets → published VData circuits and interaction probabilities, with zero-based outcome labels and classical copy as a constant-size circuit macro; reason: wire placements, total completion on malformed records, and recording the decision last preserve every physical interaction; copy is implemented using fixed preparation and reversible classical gates
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.34 (PDF p.36), Theorem G.5

import Mathlib
import Definitions.Def_GPTIP632_Classical_Supplement_Claims

set_option autoImplicit false

namespace GPTIP632.Classical.Supplement
open QAlgorithms.Complexity KTUnitary.Synth

theorem theorem_G_5 :
    ∃ (hQ : (qcPre []).Ok) (hC : (clPre []).Ok) (h3 : (qcPre [2]).Ok),
      ∀ v : Set.Ioo (0 : ℝ) 1,
        ∃ (h : (gqvPre v).Ok) (E : QEmb ((gqvPre v).toTheory h)),
          G5Conclusion v hQ hC h3 h E := by sorry

end GPTIP632.Classical.Supplement
