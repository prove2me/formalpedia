-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_lemma_9_2
-- name    : HypergraphUnreliability.FPRAS.lemma_9_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:34.672112+00:00
-- url     : https://prove2.me/theorems/c0f5c68b-adae-4425-921e-5a55f678139b
-- title:
--   Lemma 9.2 — Exact rational weighted minimum cut
-- statement:
--   Let $H$ be a connected hypergraph on $n\ge2$ vertices, with every edge having at least two vertices, and let $r^\prime_e$ be positive rational rates with a common denominator $2^a$. The value
--   $$\Lambda=\min_{\emptyset\ne S\subsetneq V}\ \sum_{e\in\partial_H S}r^\prime_e$$
--   can be computed exactly in time polynomial in the explicit input and rate encodings.
--
--   **Formalization Note** The denominator $2^a$ is written in binary, so the encoding length is at least $a$.
--
--   Differences from the source:
--   - encoding: polynomial time in the bit model → one fixed Mathlib `Turing.FinTM2` with finite alphabets and one fixed polynomial bounding its steps, chosen before the inputs; reason: a `FinTM2` step executes a bounded program fragment on a finite alphabet, so steps and bit operations agree up to a constant factor; every instance of the claim is kept
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Lemma 9.2, p. 13; (9.5), p. 13

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Instance

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- Lemma 9.2, p. 13: the value `Λ = min_{∅ ≠ S ⊊ V} ∑_{e ∈ ∂_H S} r′_e` can be computed exactly in
polynomial time in the explicit input and rate encodings. -/
theorem lemma_9_2 :
    ∃ f : RatedHypergraph → Frac,
      (∀ x, x.InDomain → 0 < (f x).den ∧ (f x).val = x.hypergraph.minCut x.rate) ∧
      PolyComputesIn RatedHypergraph.InDomain RatedHypergraph.encode (fun x => fracCode (f x))
        (fun x => x.encode.length) := by sorry

end HypergraphUnreliability.FPRAS
