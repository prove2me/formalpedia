-- Prove2me | Theorems.Thm_HopRamsey_lemma_1
-- name    : HopRamsey.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:49:44.820879+00:00
-- url     : https://prove2.me/theorems/ca4bd46a-a795-4db4-9061-b03689470511
-- title:
--   Lemma 1: $\Pr[v\notin\hat M]\le f(n,\Delta)$
-- statement:
--   Assume the standing assumptions of §4 and a valid center rule, and let the call $(X,M,\Delta)$ satisfy the call invariant, with $n=|X|$. For the output $(U,\hat M)$ of Hop-Stochastic-Embedding$(G,X,M,h,\Delta)$ and every $v\in M$,
--
--   $$
--   \Pr[v\notin\hat M]\le f(n,\Delta)=\frac4k(1+2\delta)^{\log\Delta}\Bigl(\ln n+\ln\frac2\delta\cdot\log\Delta\Bigr).
--   $$
--
--   At the root call, $f(|V|,\Phi)\le\varepsilon$ by the choice of $k$: every vertex is excluded with probability at most $\varepsilon$.
--
--   Differences from the source:
--   - generalization: the call Hop-Stochastic-Embedding(G,X,M,h,∆) made by the algorithm → every call (X, M, ∆) satisfying the call invariant X ≠ ∅, M ⊆ X, ∆ ≥ 1, diam^{(2k(L+1)h)}_G(X) ≤ ∆; reason: every call the algorithm makes satisfies the invariant (Corollary 1 and p.19, "every call ... has ∆ ≥ 1"), so the statement specializes to those calls
--   - reading: the center x_j is chosen arbitrarily; the bounds hold for every rule that determines x_j as a function of the execution so far (footnote 7, p.20) → for every `CenterRule` (a function of the call input (X, M, ∆), the phase and the call's execution so far: active set, padded set, carved balls with centers and radii) that is valid, i.e. returns a vertex satisfying line 4 whenever one exists; reason: footnote 7; a deterministic rule of the call's history is the paper's rule, and randomized rules independent of the radii follow by averaging, as footnote 7 says
--   - reading: the standing assumptions of §4 (p.14): minimum edge weight 2, |V| ≥ n ≥ 2 (p.22), ε ∈ (0,1), h ∈ [n], Φ larger than a constant → `Standing`: P.N = |V| ≥ 2, every edge weight ≥ 2, 2 ≤ Φ, 0 < ε < 1, 1 ≤ h; reason: these are the section's standing assumptions, restated as hypotheses
--   - generalization: Φ = diam^{(h)}_G(V) → Φ is any real number ≥ 2 (it enters only through k); reason: the proof uses Φ only through the value of k; the paper's Φ = diam^{(h)}_G(V) is ≥ 2 under minimum weight 2 and |V| ≥ 2, so the statement specializes to it
--   - encoding: the output (U, M̂): an HST U with X as leaves and a saved set; the random algorithm → the law (`PMF`) of the pair (d_U, M̂), with d_U : V → V → [0,∞] equal to ∞ off X; recursive calls use independent randomness; loops and recursion carry fuel that is never exhausted under the hypotheses; reason: the statements read U only through d_U; the fuel bounds are reached only by runs the hypotheses exclude (Formalization Notes of the algorithm definitions)
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), Lemma 1, p.19 (PDF p.21)

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
Lemma 1, p.19 (PDF p.21): "Let (U, M̂) be the output of the call
Hop-Stochastic-Embedding(G,X,M,h,∆), where |X| = n. Then ∀v ∈ M, Pr[v ∉ M̂] ≤ f(n,∆)."

**Formalization Note.** `f(n, ∆) = (4/k)·(1+2δ)^{log₂ ∆}·(ln n + ln(2/δ)·log₂ ∆)` (`Fig2Params.f`). For
every call satisfying the call invariant (`X ≠ ∅`, `M ⊆ X`, `∆ ≥ 1`,
`diam^{(2k(L+1)h)}_G(X) ≤ ∆`), every valid center rule, the standing assumptions of §4. The
probability is over the call's own law (the truncated algorithm). -/
theorem lemma_1 {V : Type} [Fintype V] [DecidableEq V] (P : Fig2Params) (G : WGraph V) (h : ℕ)
    (rule : CenterRule V) (hS : Standing P G h) (hrule : IsValidRule P G h rule)
    (X M : Finset V) (Δ : ℝ) (hX : CallInv P G h X M Δ) (v : V) (hv : v ∈ M) :
    (hopStochEmbedding P G h rule X M Δ).toOuterMeasure {o | v ∉ o.2} ≤
      ENNReal.ofReal (P.f X.card Δ) := by sorry

end HopRamsey
