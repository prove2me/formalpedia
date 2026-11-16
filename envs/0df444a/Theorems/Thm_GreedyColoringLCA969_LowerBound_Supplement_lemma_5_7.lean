-- Prove2me | Theorems.Thm_GreedyColoringLCA969_LowerBound_Supplement_lemma_5_7
-- name    : GreedyColoringLCA969.LowerBound.Supplement.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:38:21.227202+00:00
-- url     : https://prove2.me/theorems/042b9b13-774d-4e35-85d0-b9ba62ccd2ff
-- title:
--   Lemma 5.7 — The success-weighted number of light vertices satisfies E_G[XY] ≤ 2∆τ + bCκ with the exact decision-tree constants.
-- statement:
--   Fix integers $\Delta\ge3$, $\lambda\ge2$, $\tau\ge1$ and a deterministic standard-oracle algorithm with fixed tape. Draw the hard represented graph $G$ by selecting each group configuration independently and uniformly. Let $X$ count all light vertices and let $Y$ indicate global MIS success. Set
--
--   $$b=2\Delta\lambda,\quad q_\star=\lfloor\Delta/50\rfloor,\quad
--   D=b\sum_{h=0}^{q_\star-1}b^h,\quad C=2D+1,$$
--
--   and let $\kappa(\Delta,\lambda)$ count distinct one-group configurations. Then
--
--   $$\mathbb E_G[XY]\le2\Delta\tau+bC\kappa(\Delta,\lambda).$$
--
--   Only group configurations are averaged here, with the tape fixed. The estimate is success-weighted, not a bound on $\mathbb E[X]$ or a conditional expectation. The finite sum is empty when $q_\star=0$.
--
--   Differences from the source:
--   - encoding: vertices 1 through n and L-valued answers in the standard adjacency-list model → Fin n identifiers and injective positive-integer return codes, with success and cost derived from the immutable shared-tape execution; reason: shifting identifiers and coding labels preserves every graph, list order, question and graph-query count
--   - encoding: independent uniform group configurations and E_G[XY] → the arithmetic mean over all distinct HardInput representations, with kappa the one-group cardinality; reason: restriction to fixed blocks is a bijection to the product of one-group configurations; the spaces are finite and nonempty, so this mean is the same product expectation
--   - generalization: LCAs return Boolean labels → arbitrary positive return codes and possible nontermination; invalid codes and nontermination fail global MIS success; reason: the published machine includes all source LCAs; for Theorem 5.6 and Lemma 5.7 invalid codes can be normalized to a Boolean label without graph queries or reducing success, while the rewiring proof of Lemma 5.4 uses only equality of returned codes; infinite executions are never light
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), p. 30 (PDF 31), Lemma 5.7

import Definitions.Def_GreedyColoringLCA969_LowerBound_Supplement_HardInputs

open scoped ENNReal BigOperators
open MeasureTheory Classical
set_option autoImplicit false

namespace GreedyColoringLCA969.LowerBound.Supplement

theorem lemma_5_7 (Δ lam τ : ℕ) (hΔ : 3 ≤ Δ) (hlam : 2 ≤ lam) (hτ : 1 ≤ τ)
    (B : DeterministicLCA .standard) :
    hardExpectation Δ lam τ (fun R => successWeightedLight B R.val Δ) ≤
      (2 * Δ * τ : ℕ) + (groupSize Δ lam * decisionC Δ lam * kappa Δ lam : ℕ) := by sorry

end GreedyColoringLCA969.LowerBound.Supplement
