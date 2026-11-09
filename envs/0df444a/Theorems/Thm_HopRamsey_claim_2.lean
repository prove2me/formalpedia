-- Prove2me | Theorems.Thm_HopRamsey_claim_2
-- name    : HopRamsey.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:49:16.115292+00:00
-- url     : https://prove2.me/theorems/45955579-bcb3-43e1-852b-7f117a51d01c
-- title:
--   Claim 2: distortion $k\cdot 8L$ for saved vertices
-- statement:
--   Assume the standing assumptions of §4 and a valid center rule, and let $(X,M,\Delta)$ satisfy the call invariant. For every output $(U,\hat M)$ of Hop-Stochastic-Embedding$(G,X,M,h,\Delta)$, every $u\in\hat M$ and every $v\in X$,
--
--   $$
--   d_U(u,v)\le k\cdot 8L\cdot d^{(h)}_G(u,v).
--   $$
--
--   At the root call this is the worst-case distortion $8kL$ of the embedding for pairs containing a saved vertex.
--
--   Differences from the source:
--   - generalization: the call Hop-Stochastic-Embedding(G,X,M,h,∆) made by the algorithm → every call (X, M, ∆) satisfying the call invariant X ≠ ∅, M ⊆ X, ∆ ≥ 1, diam^{(2k(L+1)h)}_G(X) ≤ ∆; reason: every call the algorithm makes satisfies the invariant (Corollary 1 and p.19, "every call ... has ∆ ≥ 1"), so the statement specializes to those calls
--   - reading: the center x_j is chosen arbitrarily; the bounds hold for every rule that determines x_j as a function of the execution so far (footnote 7, p.20) → for every `CenterRule` (a function of the call input (X, M, ∆), the phase and the call's execution so far: active set, padded set, carved balls with centers and radii) that is valid, i.e. returns a vertex satisfying line 4 whenever one exists; reason: footnote 7; a deterministic rule of the call's history is the paper's rule, and randomized rules independent of the radii follow by averaging, as footnote 7 says
--   - reading: the standing assumptions of §4 (p.14): minimum edge weight 2, |V| ≥ n ≥ 2 (p.22), ε ∈ (0,1), h ∈ [n], Φ larger than a constant → `Standing`: P.N = |V| ≥ 2, every edge weight ≥ 2, 2 ≤ Φ, 0 < ε < 1, 1 ≤ h; reason: these are the section's standing assumptions, restated as hypotheses
--   - generalization: Φ = diam^{(h)}_G(V) → Φ is any real number ≥ 2 (it enters only through k); reason: the proof uses Φ only through the value of k; the paper's Φ = diam^{(h)}_G(V) is ≥ 2 under minimum weight 2 and |V| ≥ 2, so the statement specializes to it
--   - encoding: d^{(h)}_G as a minimum over paths with at most h hops → infimum over walks with at most h edges, in [0,∞]; reason: positive weights: removing a cycle lowers both weight and hop count, so both values agree; ∞ when no such walk exists
--   - encoding: the output (U, M̂): an HST U with X as leaves and a saved set; the random algorithm → the law (`PMF`) of the pair (d_U, M̂), with d_U : V → V → [0,∞] equal to ∞ off X; recursive calls use independent randomness; loops and recursion carry fuel that is never exhausted under the hypotheses; reason: the statements read U only through d_U; the fuel bounds are reached only by runs the hypotheses exclude (Formalization Notes of the algorithm definitions)
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), Claim 2, p.18 (PDF p.20); proof p.19 (PDF p.21)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_HopRamsey_hopDist
import Definitions.Def_HopRamsey_Fig2Params
import Definitions.Def_HopRamsey_truncGeom
import Definitions.Def_HopRamsey_singleScalePartition
import Definitions.Def_HopRamsey_hopStochEmbedding
import Definitions.Def_HopRamsey_CallInv

open scoped ENNReal

namespace HopRamsey

open ARTreeCover

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…),
Claim 2, p.18 (PDF p.20): "For every u ∈ M̂, v ∈ X, it holds that d_U(u,v) ≤ k · 8L · d^{(h)}_G(u,v)."

**Formalization Note.** For every output `(d_U, M̂)` in the support of a call `(G, X, M, h, ∆)` that
satisfies the call invariant (`X ≠ ∅`, `M ⊆ X`, `∆ ≥ 1`, `diam^{(2k(L+1)h)}_G(X) ≤ ∆`), every
valid center rule, the standing assumptions of §4. Products are in `[0, ∞]`. -/
theorem claim_2 {V : Type} [Fintype V] [DecidableEq V] (P : Fig2Params) (G : WGraph V) (h : ℕ)
    (rule : CenterRule V) (hS : Standing P G h) (hrule : IsValidRule P G h rule)
    (X M : Finset V) (Δ : ℝ) (hX : CallInv P G h X M Δ) :
    ∀ o ∈ (hopStochEmbedding P G h rule X M Δ).support, ∀ u ∈ o.2, ∀ v ∈ X,
      o.1 u v ≤ ENNReal.ofReal ((P.k : ℝ) * 8 * P.L) * hopDist G h u v := by sorry

end HopRamsey
