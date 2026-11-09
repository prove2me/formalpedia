-- Prove2me | Theorems.Thm_HopRamsey_corollary_1
-- name    : HopRamsey.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:48:53.710321+00:00
-- url     : https://prove2.me/theorems/84aa64df-5945-4453-bbfd-b2f9746388c8
-- title:
--   Corollary 1: every call has $\mathrm{diam}^{(2k(L+1)h)}_G(X)\le\Delta$, hence hop-stretch $2k(L+1)$
-- statement:
--   Assume the standing assumptions of §4, a valid center rule, and $\Phi=\mathrm{diam}^{(h)}_G(V)<\infty$. Then:
--
--   1. the root call Hop-Stochastic-Embedding$(G,V,V,h,\Phi)$ satisfies the call invariant, in particular $\mathrm{diam}^{(2k(L+1)h)}_G(V)\le\Phi$;
--   2. for every call $(X,M,\Delta)$ with $\Delta>0$, every cluster $X_i$ returned by Single-Scale-Partition satisfies $\mathrm{diam}^{(2k(L+1)h)}_G(X_i)\le\Delta/2$, so the recursive call on $(X_i,M_i,\Delta/2)$ again satisfies the diameter bound;
--   3. for every output $U$ of the root call and all $u,v\in V$,
--
--   $$
--   d_U(u,v)\ge d^{(2k(L+1)h)}_G(u,v).
--   $$
--
--   By induction, (1) and (2) say that every call made by the algorithm satisfies $\mathrm{diam}^{(2k(L+1)h)}_G(X)\le\Delta$; (3) is the hop-stretch $2k(L+1)$ of the embedding.
--
--   Differences from the source:
--   - reading: "Every time the call ... is made, it holds that diam^{(2k(L+1)h)}_G(X) ≤ ∆" → the two halves of that induction: the root call satisfies the invariant, and every cluster returned by Algorithm 2 on a call at scale ∆ > 0 has diameter ≤ ∆/2; reason: these two facts are the base case and the step of the paper's induction and together give the sentence for every call
--   - generalization: the calls made by the algorithm (step of the induction) → any X, M and any scale ∆ > 0; reason: the step uses only Observation 1, radii < k and Claim 1; it specializes to the calls the algorithm makes
--   - reading: the center x_j is chosen arbitrarily; the bounds hold for every rule that determines x_j as a function of the execution so far (footnote 7, p.20) → for every `CenterRule` (a function of the call input (X, M, ∆), the phase and the call's execution so far: active set, padded set, carved balls with centers and radii) that is valid, i.e. returns a vertex satisfying line 4 whenever one exists; reason: footnote 7; a deterministic rule of the call's history is the paper's rule, and randomized rules independent of the radii follow by averaging, as footnote 7 says
--   - reading: the standing assumptions of §4 (p.14): minimum edge weight 2, |V| ≥ n ≥ 2 (p.22), ε ∈ (0,1), h ∈ [n], Φ larger than a constant → `Standing`: P.N = |V| ≥ 2, every edge weight ≥ 2, 2 ≤ Φ, 0 < ε < 1, 1 ≤ h; reason: these are the section's standing assumptions, restated as hypotheses
--   - encoding: d^{(h)}_G as a minimum over paths with at most h hops → infimum over walks with at most h edges, in [0,∞]; reason: positive weights: removing a cycle lowers both weight and hop count, so both values agree; ∞ when no such walk exists
--   - encoding: the output (U, M̂): an HST U with X as leaves and a saved set; the random algorithm → the law (`PMF`) of the pair (d_U, M̂), with d_U : V → V → [0,∞] equal to ∞ off X; recursive calls use independent randomness; loops and recursion carry fuel that is never exhausted under the hypotheses; reason: the statements read U only through d_U; the fuel bounds are reached only by runs the hypotheses exclude (Formalization Notes of the algorithm definitions)
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), Corollary 1, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_HopRamsey_hopDist
import Definitions.Def_HopRamsey_Fig2Params
import Definitions.Def_HopRamsey_truncGeom
import Definitions.Def_HopRamsey_singleScalePartition
import Definitions.Def_HopRamsey_hopStochEmbedding
import Definitions.Def_HopRamsey_CallInv
import Definitions.Def_ARTreeCover_HST

open scoped ENNReal

namespace HopRamsey

open ARTreeCover

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…),
Corollary 1, p.18 (PDF p.20): "Every time the call Hop-Stochastic-Embedding(G,X,M,h,∆) is made, it
holds that diam^{(2k·(L+1)·h)}_G(X) ≤ ∆. In particular, for every u,v ∈ V,
d_U(u,v) ≥ d^{(2k·(L+1)·h)}_G(u,v)."

**Formalization Note.** The first sentence is stated as its two halves: (1) the root call
`(G, V, V, h, Φ)` with `Φ = diam^{(h)}_G(V) < ∞` satisfies the call invariant, and (2) every
cluster returned by Algorithm 2 on a call `(X, M, ∆)` with `∆ > 0` has
`diam^{(2k(L+1)h)}_G ≤ ∆/2`, so every child call `(X_i, M_i, ∆/2)` satisfies it in turn. (3) is the
second sentence, for every output of the root call (`d_U = ∞` off the leaves is not an issue: the
root's leaves are all of `V`). Every valid center rule, the standing assumptions of §4. -/
theorem corollary_1 {V : Type} [Fintype V] [DecidableEq V] (P : Fig2Params) (G : WGraph V) (h : ℕ)
    (rule : CenterRule V) (hS : Standing P G h) (hrule : IsValidRule P G h rule)
    (hΦfin : hopDiam G h Finset.univ ≠ ⊤) (hΦ : P.Φ = (hopDiam G h Finset.univ).toReal) :
    CallInv P G h Finset.univ Finset.univ P.Φ ∧
    (∀ (X M : Finset V) (Δ : ℝ), 0 < Δ →
      ∀ C ∈ (singleScalePartition P G h rule X M Δ).support, ∀ c ∈ C,
        hopDiam G (2 * P.k * (P.L + 1) * h) c.1 ≤ ENNReal.ofReal (Δ / 2)) ∧
    (∀ o ∈ (hopStochEmbedding P G h rule Finset.univ Finset.univ P.Φ).support, ∀ u v : V,
      hopDist G (2 * P.k * (P.L + 1) * h) u v ≤ o.1 u v) := by sorry

end HopRamsey
