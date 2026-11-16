-- Prove2me | Theorems.Thm_GreedyColoringLCA969_LowerBound_Supplement_lemma_5_4
-- name    : GreedyColoringLCA969.LowerBound.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:37:40.282561+00:00
-- url     : https://prove2.me/theorems/90c8a66c-147b-45fd-94e0-b22e37af5164
-- title:
--   Lemma 5.4 — Fixing every other group, more than 2∆ light vertices in one configuration forces a bad pair in another configuration of that group.
-- statement:
--   Fix integers $\Delta\ge3$, $\lambda\ge2$, $\tau\ge1$, a deterministic standard-oracle algorithm with fixed tape, a group $i$, and all the other groups' configurations in the hard construction of §5.1. Let $b=2\Delta\lambda$ and $q_\star=\lfloor\Delta/50\rfloor$. If some configuration of group $i$ has strictly more than $2\Delta$ light vertices, then some configuration of that group has a bad pair:
--
--   $$\exists\text{ configuration with }>2\Delta\text{ light vertices}
--   \ \Longrightarrow\ \exists\text{ configuration with a bad pair}.$$
--
--   Every other group's ordered adjacency lists remain fixed. Lightness and return labels come from the actual executions; queries into other groups are allowed. The conclusion provides the obstruction used in the MIS lower bound, including the zero-query lightness regime.
--
--   Differences from the source:
--   - encoding: vertices 1 through n and L-valued answers in the standard adjacency-list model → Fin n identifiers and injective positive-integer return codes, with success and cost derived from the immutable shared-tape execution; reason: shifting identifiers and coding labels preserves every graph, list order, question and graph-query count
--   - encoding: independently configurable groups and a pair in one biclique → HardInput is a subtype of represented graphs; SameOutside fixes all other lists, and adjacency/equal neighbor sets recognize opposite/same sides; reason: decomposition witnesses are not sampled or stored; for Delta>=3 this recognition is exactly biclique membership
--   - generalization: LCAs return Boolean labels → arbitrary positive return codes and possible nontermination; invalid codes and nontermination fail global MIS success; reason: the published machine includes all source LCAs; for Theorem 5.6 and Lemma 5.7 invalid codes can be normalized to a Boolean label without graph queries or reducing success, while the rewiring proof of Lemma 5.4 uses only equality of returned codes; infinite executions are never light
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), p. 28 (PDF 29), Lemma 5.4

import Definitions.Def_GreedyColoringLCA969_LowerBound_Supplement_HardInputs

open scoped ENNReal BigOperators
open MeasureTheory Classical
set_option autoImplicit false

namespace GreedyColoringLCA969.LowerBound.Supplement

theorem lemma_5_4 (Δ lam τ : ℕ) (hΔ : 3 ≤ Δ) (hlam : 2 ≤ lam) (hτ : 1 ≤ τ)
    (B : DeterministicLCA .standard) (i : Fin τ) (R : HardInput Δ lam τ)
    (hmany : 2 * Δ < groupLightCount B R.val Δ lam i.val) :
    ∃ S : HardInput Δ lam τ, SameOutside R.val S.val Δ lam i.val ∧
      ∃ v w : Fin (hardSize Δ lam τ), v.val / groupSize Δ lam = i.val ∧
        w.val / groupSize Δ lam = i.val ∧ BadPair B S.val Δ v w := by sorry

end GreedyColoringLCA969.LowerBound.Supplement
