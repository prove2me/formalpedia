-- Prove2me | Theorems.Thm_GPTIP632_Classical_Supplement_lemma_F_9
-- name    : GPTIP632.Classical.Supplement.lemma_F_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:24:33.525947+00:00
-- url     : https://prove2.me/theorems/2a2bba8a-9106-4c81-90d4-1a40113234fa
-- title:
--   Lemma F.9 — In quantum theory with classical systems (optionally with finitely many Δ_d adjoined, standard coordinates and gates), arbitrary messages give no
-- statement:
--   The source result is:
--
--   Lemma F.9 (Classical registers as messages in quantum theory). Let QC be quantum theory with
--   classical systems, possibly with finitely many classical systems $\Delta_d$ of fixed dimensions adjoined as
--   elementary systems, each with its standard coordinates and with the gates preparation of $\delta_1$, readout
--   of the label and discard. Then $\mathsf{GIP}(\mathsf{QC}; k) = \mathsf{QIP}(k)$ for every $k$, and $\mathsf{GIP}(\mathsf{QC}) = \mathsf{QIP} = \mathsf{PSPACE}$.
--   The fixed-message equality holds with any fixed thresholds $0 < s < c < 1$ imposed on both sides; for
--   polynomially many messages these thresholds give the same class $\mathsf{PSPACE}$.
--
--   For every finite list ds of dimensions d (each ≥ 1) of adjoined classical elementary systems Δ_d (QC_ds; ds = [] is QC itself): GIP(QC_ds; k) = QIP(k) for every k; GIP(QC_ds) = QIP; QIP = PSPACE; and for every pair of real constants 0 < s < c < 1: GIP_{c,s}(QC_ds; k) = QIP_{c,s}(k) for every k and GIP_{c,s}(QC_ds) = PSPACE. Every clause.
--
--   The concrete systems, gates, class definitions and any conclusion predicates are defined by the supplement interfaces. Completeness is at least 2/3 and soundness is at most 1/3, except for the explicitly quantified 0 < s < c < 1 clause of Lemma F.9. Every fixed message bound means at most k messages, counting both directions. No simulation theorem or class equality is assumed.
--
--   Differences from the source:
--   - encoding: finite-dimensional systems, composites and quantum channels in fixed bases → real coordinate frames, binary-tree register presentations (including a labelled copy of Delta_3), Kraus gate matrices and complete positivity on every ancilla dimension; reason: these represent the same quantum, classical and transported cones; labels and parentheses carry no operational data
--   - encoding: the explicitly defined QC, classical and triangular theories are valid theories → existential proofs of PreTheory.Ok package the fixed concrete data into the published Theory type; reason: validity is a conclusion, not an added hypothesis; proof irrelevance makes all such proof witnesses describe exactly the same theory
--   - encoding: any finite list of adjoined positive-dimensional classical systems Delta_d → an arbitrary list ds whose entry n denotes Delta_(n+1); reason: offset indexing covers exactly all positive dimensions, including the empty list and dimension one
--   - encoding: adaptive quantum or classical circuits in the source gate sets → published VData circuits and interaction probabilities, with zero-based outcome labels and classical copy as a constant-size circuit macro; reason: wire placements, total completion on malformed records, and recording the decision last preserve every physical interaction; copy is implemented using fixed preparation and reversible classical gates
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.31 (PDF p.33), Lemma F.9

import Mathlib
import Definitions.Def_GPTIP632_Classical_Supplement_Claims

set_option autoImplicit false

namespace GPTIP632.Classical.Supplement
open QAlgorithms.Complexity KTUnitary.Synth

theorem lemma_F_9 :
    ∃ hQ : (qcPre []).Ok,
      ∀ ds : List ℕ, ∃ h : (qcPre ds).Ok,
        ((qcPre ds).toTheory h).Standing ∧
        (∀ k : ℕ, GIPk ((qcPre ds).toTheory h) k = QIPk hQ k) ∧
        GIP ((qcPre ds).toTheory h) = QIP hQ ∧ QIP hQ = PromisePSPACE O₀ ∧
        ∀ s c : ℝ, 0 < s → s < c → c < 1 →
          (∀ k : ℕ, GIPgen ((qcPre ds).toTheory h) c s k = QIPgen hQ c s k) ∧
          GIPgen ((qcPre ds).toTheory h) c s ⊤ = PromisePSPACE O₀ := by sorry

end GPTIP632.Classical.Supplement
