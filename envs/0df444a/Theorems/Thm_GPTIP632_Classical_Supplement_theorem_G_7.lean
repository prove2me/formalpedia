-- Prove2me | Theorems.Thm_GPTIP632_Classical_Supplement_theorem_G_7
-- name    : GPTIP632.Classical.Supplement.theorem_G_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:26:54.800712+00:00
-- url     : https://prove2.me/theorems/311387a0-ae99-4c89-b41b-e974c1bccb7c
-- title:
--   Theorem G.7 — For T as in the unary space hierarchy (Fact G
-- statement:
--   The source result is:
--
--   Theorem G.7 (A computable coordinate outside polynomial space). Let $T$ be as in Fact G.6,
--   modified to contain 0, and let $v_T = \sum_{i\in T} 4^{-i-1} \in [\frac14, \frac13]$. Then:
--     (i) $v_T$ is computable; the state cones of $\mathcal G_{v_T}$ and of $\mathcal G^{\mathrm Q}_{v_T}$ have finite descriptions by linear or
--         positive-semidefinite constraints with computable coefficients, and their unit effects, verifier
--         gates and isomorphisms with classical theory and with $\mathsf{QC}$ have computable entries;
--    (ii) $L_{v_T} \in \mathsf{GMA}(\mathcal G_{v_T}) \cap \mathsf{GMA}(\mathcal G^{\mathrm Q}_{v_T})$;
--   (iii) $L_{v_T} \notin \mathsf{PSPACE}$;
--    (iv) $L_{v_T}$ is decidable, in space $2^{O(\log^2 m)}$ on inputs of length $m$.
--   Consequently $\mathsf{GIP}(\mathcal G_{v_T}) \supsetneq \mathsf{PSPACE}$ and $\mathsf{GIP}(\mathcal G^{\mathrm Q}_{v_T}) \supsetneq \mathsf{PSPACE}$ unconditionally, although both theories
--   have computable presentations, $\mathcal G^{\mathrm Q}_{v_T}$ contains quantum theory and classical theory, $\mathsf{GIP}_{\mathrm{cl}} = \mathsf{PSPACE}$
--   in both, and $\mathsf{GIP}_{\mathrm{qm}}(\mathcal G^{\mathrm Q}_{v_T}) = \mathsf{PSPACE}$.
--
--   Conjunction of: (A) for every T ⊆ ℕ with 0 ∈ T, {1^n : n ∈ T} ∈ DSPACE(2^{n²}) and {1^n : n ∈ T} ∉ DSPACE(2^{cn}) for every constant c (DSPACE(f) = decidable by an OTM, empty oracle, halting on every input within space C·f(n)+C for some constant C), with v_T := Σ_{i∈T} 4^{−i−1}: v_T ∈ [1/4, 1/3] and (i)–(iv) and every consequence clause; and (B) such a T exists (Fact G.6 plus adding 0; App. I). (B) is what makes 'unconditionally' non-vacuous; do not drop it. (iv): ∃ c and an OTM halting on every input, accepting L_{v_T},yes and rejecting L_{v_T},no, using at most 2^{c·(Nat.log 2 m + 1)^2} cells on every input of length m. (i): reading in pitfalls.
--
--   The concrete systems, gates, class definitions and any conclusion predicates are defined by the supplement interfaces. Completeness is at least 2/3 and soundness is at most 1/3, except for the explicitly quantified 0 < s < c < 1 clause of Lemma F.9. Every fixed message bound means at most k messages, counting both directions. No simulation theorem or class equality is assumed.
--
--   Differences from the source:
--   - encoding: finite-dimensional systems, composites and quantum channels in fixed bases → real coordinate frames, binary-tree register presentations (including a labelled copy of Delta_3), Kraus gate matrices and complete positivity on every ancilla dimension; reason: these represent the same quantum, classical and transported cones; labels and parentheses carry no operational data
--   - encoding: the explicitly defined QC, classical and triangular theories are valid theories → existential proofs of PreTheory.Ok package the fixed concrete data into the published Theory type; reason: validity is a conclusion, not an added hypothesis; proof irrelevance makes all such proof witnesses describe exactly the same theory
--   - encoding: computable coordinate, computable presentations, unary hierarchy and space 2^{O(log^2 m)} → published computable reals, Mathlib-Computable promise deciders, empty-oracle total OTMs, and a uniform existential c with bound 2^(c*(Nat.log 2 m+1)^2); reason: these give the same computability and space notions, with input cells counted and small lengths covered; natural constants are cofinal
--   - encoding: T as in Fact G.6, modified to contain zero, giving an unconditional separation → existence of such a T and the complete result for every T with zero and both hierarchy properties; reason: the existence conjunct retains the unconditional assertion; no hierarchy assumption replaces its existence
--   - encoding: adaptive quantum or classical circuits in the source gate sets → published VData circuits and interaction probabilities, with zero-based outcome labels and classical copy as a constant-size circuit macro; reason: wire placements, total completion on malformed records, and recording the decision last preserve every physical interaction; copy is implemented using fixed preparation and reversible classical gates
--   - reading: state cones have finite linear or PSD descriptions with computable coefficients, and the isomorphisms have computable entries → each classical-triangular system has finitely many computable linear inequalities; each quantum-triangular system has a Hermitian PSD pencil with computable entries; both isomorphism directions have computable matrices; reason: the reading specified in BRIEF.json makes the per-system descriptions explicit and follows the transport formulas of Example B.23
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.35 (PDF p.37), Theorem G.7

import Mathlib
import Definitions.Def_GPTIP632_Classical_Supplement_Claims

set_option autoImplicit false

namespace GPTIP632.Classical.Supplement
open QAlgorithms.Complexity KTUnitary.Synth

theorem theorem_G_7 :
    (∃ T : Set ℕ, 0 ∈ T ∧ UnaryHierarchy T) ∧
      ∃ (hQ : (qcPre []).Ok) (hC3 : (clPre [2]).Ok) (hQ3 : (qcPre [2]).Ok),
        ∀ T : Set ℕ, 0 ∈ T → UnaryHierarchy T →
          ∃ (hv : vT T ∈ Set.Ioo (0 : ℝ) 1),
            (1 : ℝ) / 4 ≤ vT T ∧ vT T ≤ 1 / 3 ∧
            ∃ (h : (gvPre ⟨vT T, hv⟩).Ok) (h' : (gqvPre ⟨vT T, hv⟩).Ok)
              (E : QEmb ((gqvPre ⟨vT T, hv⟩).toTheory h')),
              G7Conclusion T hv hQ hC3 hQ3 h h' E := by sorry

end GPTIP632.Classical.Supplement
