-- Prove2me | Theorems.Thm_HopRamsey_lemma_2
-- name    : HopRamsey.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:49:30.184466+00:00
-- url     : https://prove2.me/theorems/7284beb3-54fb-40dc-bbbc-63514a901b54
-- title:
--   Lemma 2: expected distortion $g(n,\Delta)$
-- statement:
--   Assume the standing assumptions of §4 and a valid center rule, and let the call $(X,M,\Delta)$ satisfy the call invariant, with $n=|X|$. For the output $(U,\hat M)$ of Hop-Stochastic-Embedding$(G,X,M,h,\Delta)$ and all $u,v\in X$,
--
--   $$
--   \mathbb E\bigl[d_{U,\hat M}(u,v)\bigr]\le g(n,\Delta)\cdot d^{(h)}_G(u,v),\qquad g(n,\Delta)=2^8\,L\,\log n\,(1+2\delta)^{\log\Delta},
--   $$
--
--   where $d_{U,\hat M}(u,v)=d_U(u,v)$ if $u,v\in\hat M$ and $0$ otherwise. At the root call $g(|V|,\Phi)=\tilde O(\log n)$, independent of $\varepsilon$.
--
--   Differences from the source:
--   - generalization: the call Hop-Stochastic-Embedding(G,X,M,h,∆) made by the algorithm → every call (X, M, ∆) satisfying the call invariant X ≠ ∅, M ⊆ X, ∆ ≥ 1, diam^{(2k(L+1)h)}_G(X) ≤ ∆; reason: every call the algorithm makes satisfies the invariant (Corollary 1 and p.19, "every call ... has ∆ ≥ 1"), so the statement specializes to those calls
--   - reading: the center x_j is chosen arbitrarily; the bounds hold for every rule that determines x_j as a function of the execution so far (footnote 7, p.20) → for every `CenterRule` (a function of the call input (X, M, ∆), the phase and the call's execution so far: active set, padded set, carved balls with centers and radii) that is valid, i.e. returns a vertex satisfying line 4 whenever one exists; reason: footnote 7; a deterministic rule of the call's history is the paper's rule, and randomized rules independent of the radii follow by averaging, as footnote 7 says
--   - reading: the standing assumptions of §4 (p.14): minimum edge weight 2, |V| ≥ n ≥ 2 (p.22), ε ∈ (0,1), h ∈ [n], Φ larger than a constant → `Standing`: P.N = |V| ≥ 2, every edge weight ≥ 2, 2 ≤ Φ, 0 < ε < 1, 1 ≤ h; reason: these are the section's standing assumptions, restated as hypotheses
--   - generalization: Φ = diam^{(h)}_G(V) → Φ is any real number ≥ 2 (it enters only through k); reason: the proof uses Φ only through the value of k; the paper's Φ = diam^{(h)}_G(V) is ≥ 2 under minimum weight 2 and |V| ≥ 2, so the statement specializes to it
--   - encoding: d^{(h)}_G as a minimum over paths with at most h hops → infimum over walks with at most h edges, in [0,∞]; reason: positive weights: removing a cycle lowers both weight and hop count, so both values agree; ∞ when no such walk exists
--   - encoding: the output (U, M̂): an HST U with X as leaves and a saved set; the random algorithm → the law (`PMF`) of the pair (d_U, M̂), with d_U : V → V → [0,∞] equal to ∞ off X; recursive calls use independent randomness; loops and recursion carry fuel that is never exhausted under the hypotheses; reason: the statements read U only through d_U; the fuel bounds are reached only by runs the hypotheses exclude (Formalization Notes of the algorithm definitions)
--   - encoding: E[d_{U,M̂}(u,v)] → the [0,∞]-valued sum over the output law of the mass times (d_U(u,v) if u,v ∈ M̂, else 0); reason: the expectation of a nonnegative variable over a discrete law; infinite values outside M̂ × M̂ contribute 0, as the paper specifies
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), Lemma 2, p.22 (PDF p.24)

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
Lemma 2, p.22 (PDF p.24): "Let (U, M̂) be the output of the call
Hop-Stochastic-Embedding(G,X,M,h,∆), where |X| = n. Then for every u,v ∈ X,
E[d_{U,M̂}(u,v)] ≤ g(n,∆) · d^{(h)}_G(u,v)."

**Formalization Note.** `g(n, ∆) = 2⁸·L·log₂ n·(1+2δ)^{log₂ ∆}` (`Fig2Params.g`);
`d_{U,M̂}(u, v) = d_U(u, v)` if `u, v ∈ M̂` and `0` otherwise, written as an `if` inside the
`[0, ∞]`-valued sum over the call's law. For every call satisfying the call invariant, every valid
center rule, the standing assumptions of §4. -/
theorem lemma_2 {V : Type} [Fintype V] [DecidableEq V] (P : Fig2Params) (G : WGraph V) (h : ℕ)
    (rule : CenterRule V) (hS : Standing P G h) (hrule : IsValidRule P G h rule)
    (X M : Finset V) (Δ : ℝ) (hX : CallInv P G h X M Δ) (u v : V) (hu : u ∈ X) (hv : v ∈ X) :
    (∑' o, (hopStochEmbedding P G h rule X M Δ) o * (if u ∈ o.2 ∧ v ∈ o.2 then o.1 u v else 0)) ≤
      ENNReal.ofReal (P.g X.card Δ) * hopDist G h u v := by sorry

end HopRamsey
