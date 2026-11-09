-- Prove2me | Theorems.Thm_HopRamsey_claim_1
-- name    : HopRamsey.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:48:17.490184+00:00
-- url     : https://prove2.me/theorems/b3c69167-6115-4b78-abb7-314160d43a9e
-- title:
--   Claim 1: the last cluster has $\mathrm{diam}^{(2k(L+1)h)}_G(X_0)\le 2r_L\le\Delta/2$
-- statement:
--   Run Algorithm 2 on $(G,X,M,h,\Delta)$ under the standing assumptions of §4, with any valid center rule and $\Delta>0$. On every run, if the last cluster $X_0$ (the vertices still active after phase $1$) is nonempty, then
--
--   $$
--   \mathrm{diam}^{(2k(L+1)h)}_G(X_0)\le 2r_L\le\frac\Delta2 .
--   $$
--
--   Together with the bound on carved balls this shows that every child call of Algorithm 1 again satisfies the diameter invariant, at half the scale. It holds on every run, whatever radii were drawn.
--
--   Differences from the source:
--   - reading: the center x_j is chosen arbitrarily; the bounds hold for every rule that determines x_j as a function of the execution so far (footnote 7, p.20) → for every `CenterRule` (a function of the call input (X, M, ∆), the phase and the call's execution so far: active set, padded set, carved balls with centers and radii) that is valid, i.e. returns a vertex satisfying line 4 whenever one exists; reason: footnote 7; a deterministic rule of the call's history is the paper's rule, and randomized rules independent of the radii follow by averaging, as footnote 7 says
--   - reading: the standing assumptions of §4 (p.14): minimum edge weight 2, |V| ≥ n ≥ 2 (p.22), ε ∈ (0,1), h ∈ [n], Φ larger than a constant → `Standing`: P.N = |V| ≥ 2, every edge weight ≥ 2, 2 ≤ Φ, 0 < ε < 1, 1 ≤ h; reason: these are the section's standing assumptions, restated as hypotheses
--   - generalization: Φ = diam^{(h)}_G(V) → Φ is any real number ≥ 2 (it enters only through k); reason: the proof uses Φ only through the value of k; the paper's Φ = diam^{(h)}_G(V) is ≥ 2 under minimum weight 2 and |V| ≥ 2, so the statement specializes to it
--   - generalization: a call of Algorithm 2 made by Algorithm 1 → any X, M and any scale ∆ > 0 (no call invariant); reason: the proof uses only the choice of centers and µ_0 > |V| ≥ n; it specializes to the calls the algorithm makes
--   - encoding: d^{(h)}_G as a minimum over paths with at most h hops → infimum over walks with at most h edges, in [0,∞]; reason: positive weights: removing a cycle lowers both weight and hop count, so both values agree; ∞ when no such walk exists
--   - encoding: the output (U, M̂): an HST U with X as leaves and a saved set; the random algorithm → the law (`PMF`) of the pair (d_U, M̂), with d_U : V → V → [0,∞] equal to ∞ off X; recursive calls use independent randomness; loops and recursion carry fuel that is never exhausted under the hypotheses; reason: the statements read U only through d_U; the fuel bounds are reached only by runs the hypotheses exclude (Formalization Notes of the algorithm definitions)
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), Claim 1, p.17 (PDF p.19); proof p.18 (PDF p.20)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_HopRamsey_hopDist
import Definitions.Def_HopRamsey_Fig2Params
import Definitions.Def_HopRamsey_truncGeom
import Definitions.Def_HopRamsey_singleScalePartition
import Definitions.Def_HopRamsey_CallInv

open scoped ENNReal

namespace HopRamsey

open ARTreeCover

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…),
Claim 1, p.17 (PDF p.19): "The last created cluster X_0, if nonempty, has
diam^{(2k·(L+1)·h)}_G(X_0) ≤ 2r_L ≤ ∆/2."

**Formalization Note.** `X_0` is the active set of a final state in the support of the run of
Algorithm 2 on `(G, X, M, h, ∆)`; every valid center rule, the standing assumptions of §4, `∆ > 0`.
The diameter is in `[0, ∞]`. -/
theorem claim_1 {V : Type} [Fintype V] [DecidableEq V] (P : Fig2Params) (G : WGraph V) (h : ℕ)
    (rule : CenterRule V) (hS : Standing P G h) (hrule : IsValidRule P G h rule)
    (X M : Finset V) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∀ s ∈ (sspRun P G h rule X M Δ).support, s.active.Nonempty →
      hopDiam G (2 * P.k * (P.L + 1) * h) s.active ≤ ENNReal.ofReal (2 * P.r Δ P.L) ∧
        2 * P.r Δ P.L ≤ Δ / 2 := by sorry

end HopRamsey
