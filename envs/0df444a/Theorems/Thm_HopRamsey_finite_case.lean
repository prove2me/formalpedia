-- Prove2me | Theorems.Thm_HopRamsey_finite_case
-- name    : HopRamsey.finite_case
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:49:39.542488+00:00
-- url     : https://prove2.me/theorems/325a91c7-381b-416d-8048-6bf8a37531a7
-- title:
--   Conclusion of §4.3: the finite case with hop-stretch $2k(L+1)$, distortion $8kL$, exclusion $f\le\varepsilon$, expected distortion $g$
-- statement:
--   Assume the standing assumptions of §4 (minimum edge weight $2$, $|V|\ge2$, $h\ge1$, $\varepsilon\in(0,1)$), a valid center rule, and that $\Phi=\mathrm{diam}^{(h)}_G(V)$ is finite. The output of the root call Hop-Stochastic-Embedding$(G,V,V,h,\Phi)$ is a distribution over pairs (HST on all of $V$, saved set), and it has
--
--   1. hop-stretch $2k(L+1)$;
--   2. distortion $k\cdot8L$;
--   3. exclusion probability $f(|V|,\Phi)$, and $f(|V|,\Phi)\le\varepsilon$;
--   4. expected distortion $g(|V|,\Phi)$.
--
--   Combined with the parameter bounds (the companion milestone) this is Theorem 1 for graphs of finite $h$-hop diameter.
--
--   Differences from the source:
--   - reading: "(U, M̂) ... U has hop-stretch ..." for the output of the algorithm, a random HST → there is a law D on pairs (HST with leaf set V, saved set) whose image under (U, M̂) ↦ (d_U, M̂) is the output law of the root call, and D has the four properties; reason: the output law is a law on ultrametrics with leaves V; D presents it as a distribution over HSTs as Definition 2 requires
--   - generalization: the conclusion assumes all edge weights are polynomial → no bound on the weights; reason: the explicit parameters 2k(L+1), 8kL, f, g do not need it; it is only used for the Õ forms (finite_case_parameters)
--   - reading: the center x_j is chosen arbitrarily; the bounds hold for every rule that determines x_j as a function of the execution so far (footnote 7, p.20) → for every `CenterRule` (a function of the call input (X, M, ∆), the phase and the call's execution so far: active set, padded set, carved balls with centers and radii) that is valid, i.e. returns a vertex satisfying line 4 whenever one exists; reason: footnote 7; a deterministic rule of the call's history is the paper's rule, and randomized rules independent of the radii follow by averaging, as footnote 7 says
--   - reading: the standing assumptions of §4 (p.14): minimum edge weight 2, |V| ≥ n ≥ 2 (p.22), ε ∈ (0,1), h ∈ [n], Φ larger than a constant → `Standing`: P.N = |V| ≥ 2, every edge weight ≥ 2, 2 ≤ Φ, 0 < ε < 1, 1 ≤ h; reason: these are the section's standing assumptions, restated as hypotheses
--   - encoding: d^{(h)}_G as a minimum over paths with at most h hops → infimum over walks with at most h edges, in [0,∞]; reason: positive weights: removing a cycle lowers both weight and hop count, so both values agree; ∞ when no such walk exists
--   - encoding: the output (U, M̂): an HST U with X as leaves and a saved set; the random algorithm → the law (`PMF`) of the pair (d_U, M̂), with d_U : V → V → [0,∞] equal to ∞ off X; recursive calls use independent randomness; loops and recursion carry fuel that is never exhausted under the hypotheses; reason: the statements read U only through d_U; the fuel bounds are reached only by runs the hypotheses exclude (Formalization Notes of the algorithm definitions)
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), Conclusion of §4.3, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_HopRamsey_hopDist
import Definitions.Def_HopRamsey_Fig2Params
import Definitions.Def_HopRamsey_truncGeom
import Definitions.Def_HopRamsey_singleScalePartition
import Definitions.Def_HopRamsey_hopStochEmbedding
import Definitions.Def_HopRamsey_CallInv
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_HopRamsey_IsStochRamseyEmbedding

open scoped ENNReal

namespace HopRamsey

open ARTreeCover

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…),
Conclusion of §4.3 (finite case), p.25 (PDF p.27): "Let (U, M̂) be the output of the call
Hop-Stochastic-Embedding(G,V,V,h,Φ), and denote |V| = n. Recall that we are assuming that
Φ = diam^{(h)}_G(V) is finite [...]. By Corollary 1, U has hop-stretch 2k·(L+1) [...]. By Claim 2,
U has distortion k·8L [...]. By Lemma 1, for every v ∈ V, the probability that v is not included is
at most Pr[v ∉ M̂] ≤ f(n,Φ) [...] ≤ ε. By Lemma 2, the expected distortion is bounded by g(n,Φ)."

**Formalization Note.** The output law of the root call is the image of a law `D` on HSTs with
leaf set `V` and saved sets ("into HSTs"), and `D` has the four properties of Definition 2 with
the explicit parameters. Standing assumptions of §4 (minimum edge weight `2`, `|V| ≥ 2`, `h ≥ 1`,
`ε ∈ (0,1)`), every valid center rule, `Φ = diam^{(h)}_G(V) < ∞`. The `Õ` forms of these
parameters are the companion milestone `finite_case_parameters`. -/
theorem finite_case {V : Type} [Fintype V] [DecidableEq V] (P : Fig2Params) (G : WGraph V) (h : ℕ)
    (rule : CenterRule V) (hS : Standing P G h) (hrule : IsValidRule P G h rule)
    (hΦfin : hopDiam G h Finset.univ ≠ ⊤) (hΦ : P.Φ = (hopDiam G h Finset.univ).toReal) :
    ∃ D : PMF (HST V × Finset V), (∀ x ∈ D.support, x.1.leaves = Set.univ) ∧
      D.map (fun x => (x.1.ρ, x.2)) =
        hopStochEmbedding P G h rule Finset.univ Finset.univ P.Φ ∧
      HasHopStretch G h D (2 * P.k * (P.L + 1)) ∧
      HasDistortion G h D ((P.k : ℝ) * 8 * P.L) ∧
      HasExclusion D (P.f P.N P.Φ) ∧ P.f P.N P.Φ ≤ P.ε ∧
      HasExpectedDistortion G h D (P.g P.N P.Φ) := by sorry

end HopRamsey
