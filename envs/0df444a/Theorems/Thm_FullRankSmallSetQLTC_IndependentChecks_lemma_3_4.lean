-- Prove2me | Theorems.Thm_FullRankSmallSetQLTC_IndependentChecks_lemma_3_4
-- name    : FullRankSmallSetQLTC.IndependentChecks.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:47.729315+00:00
-- url     : https://prove2.me/theorems/abbff0b9-e6ac-4f08-8520-e9bb2a0fd302
-- title:
--   Lemma 3.4 — injectivity and surjectivity are detected on the orbit matrix
-- statement:
--   Let $\Gamma$ be a finite bipartite graph on $L\sqcup R$ with binary adjacency map $A:\mathbb F_2^L\to\mathbb F_2^R$, and suppose Assumption 3.1: a finite $2$-group $G$ acts freely on $L$ and on $R$ (preserving the two classes) and preserves the edges. Let $[A]:\mathbb F_2^{L/G}\to\mathbb F_2^{R/G}$ be the orbit matrix, the adjacency map of the quotient graph $\Gamma/G$ (edge orbits counted modulo 2). Then
--   $$A\text{ injective}\iff[A]\text{ injective},\qquad A\text{ surjective}\iff[A]\text{ surjective}.$$
--
--   This reduces the rank conditions on growing graphs to a matrix of fixed size.
--
--   Differences from the source:
--   - encoding: a finite 2-group G acting freely, preserving vertex classes and edges → IsPGroup 2 G with Finite G; separate free actions on L and R; edge invariance; reason: same hypotheses; separate actions on the two classes preserve them
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), Lemma 3.4, p. 15 (Assumption 3.1 p. 12, §3.2 p. 14) (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Graph

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open MulAction

open Classical in
/-- **Lemma 3.4** (p. 15). Let `Γ` be a finite bipartite graph on `L ⊔ R` with adjacency map
`A : 𝔽₂^L → 𝔽₂^R`, and let a finite `2`-group `G` act freely on `L` and on `R`, preserving the
edges (Assumption 3.1). Then `A` is injective iff its orbit matrix `[A]` is injective, and `A`
is surjective iff `[A]` is surjective. -/
theorem lemma_3_4 {G L R : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    [MulAction G L] [MulAction G R] [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (adj : L → R → Prop) [DecidableRel adj]
    (hL : IsFreeAction G L) (hR : IsFreeAction G R) (hinv : IsInvariantRel G adj) :
    (Function.Injective (adjMatrix adj).mulVec ↔
        Function.Injective (orbitMatrix G adj).mulVec) ∧
    (Function.Surjective (adjMatrix adj).mulVec ↔
        Function.Surjective (orbitMatrix G adj).mulVec) := by sorry

end FullRankSmallSetQLTC.IndependentChecks
