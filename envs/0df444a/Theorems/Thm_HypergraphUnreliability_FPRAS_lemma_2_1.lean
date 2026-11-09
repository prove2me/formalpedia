-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_lemma_2_1
-- name    : HypergraphUnreliability.FPRAS.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:44.286954+00:00
-- url     : https://prove2.me/theorems/8c4a9776-be2c-4a70-b80b-15e7a4be55bc
-- title:
--   Lemma 2.1 — Polynomial-time unweighted hypergraph minimum cut
-- statement:
--   For an explicit hypergraph on $n\ge2$ vertices, the integer
--   $$\lambda=\min_{\emptyset\ne S\subsetneq V}|\partial_H S|,$$
--   counting edge labels, including parallel edges, is computable in time polynomial in the explicit hypergraph input length.
--
--   The rank is unrestricted. This is the preprocessing step of the common-probability algorithm.
--
--   Differences from the source:
--   - encoding: polynomial time in the bit model → one fixed Mathlib `Turing.FinTM2` with finite alphabets and one fixed polynomial bounding its steps, chosen before the inputs; reason: a `FinTM2` step executes a bounded program fragment on a finite alphabet, so steps and bit operations agree up to a constant factor; every instance of the claim is kept
--   - encoding: edges after the discarding of §1.1 → raw incidence lists, possibly with repeats and empty or singleton edges; reason: such labels cross no set, so $\lambda$ is unchanged; the input length only increases
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Lemma 2.1, p. 4

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Instance

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- Lemma 2.1, p. 4: for `n ≥ 2`, the integer `λ = min_{∅ ≠ S ⊊ V} |∂_H S|`, counting edge labels, is
computable in time polynomial in the explicit hypergraph input length. -/
theorem lemma_2_1 :
    PolyComputesIn (fun x : RawHypergraph => 2 ≤ x.n) RawHypergraph.encode
      (fun x => natCode x.hypergraph.minCutCount) (fun x => x.encode.length) := by sorry

end HypergraphUnreliability.FPRAS
