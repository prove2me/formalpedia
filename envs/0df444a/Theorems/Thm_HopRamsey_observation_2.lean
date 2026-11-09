-- Prove2me | Theorems.Thm_HopRamsey_observation_2
-- name    : HopRamsey.observation_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:47:37.547079+00:00
-- url     : https://prove2.me/theorems/b54fa2d0-5c1a-4441-8d73-008c4292316e
-- title:
--   Observation 2: at most $\mu_{\ell-1}$ balls per phase, each of size at most $n/\mu_\ell$
-- statement:
--   Run Algorithm 2 (Single-Scale-Partition) on $(G,X,M,h,\Delta)$ with $n=|X|$, under the standing assumptions of §4, with any valid center rule and $\Delta>0$. On every run, for every phase $1\le\ell\le L$:
--
--   1. at most $\mu_{\ell-1}$ balls are carved during phase $\ell$;
--   2. every cluster created during phase $\ell$ has at most $n/\mu_\ell$ vertices.
--
--   The second part is what lets the induction of Lemmas 1 and 2 descend from $n$ to $n/\mu_\ell$; the first bounds the number of tape entries the analysis needs per phase.
--
--   Differences from the source:
--   - reading: a statement about the phases of a run of Algorithm 2 → for every final state in the support of the run, counting its carved balls tagged with phase ℓ, for 1 ≤ ℓ ≤ L; reason: the run records each carved ball with its phase
--   - reading: the center x_j is chosen arbitrarily; the bounds hold for every rule that determines x_j as a function of the execution so far (footnote 7, p.20) → for every `CenterRule` (a function of the call input (X, M, ∆), the phase and the call's execution so far: active set, padded set, carved balls with centers and radii) that is valid, i.e. returns a vertex satisfying line 4 whenever one exists; reason: footnote 7; a deterministic rule of the call's history is the paper's rule, and randomized rules independent of the radii follow by averaging, as footnote 7 says
--   - reading: the standing assumptions of §4 (p.14): minimum edge weight 2, |V| ≥ n ≥ 2 (p.22), ε ∈ (0,1), h ∈ [n], Φ larger than a constant → `Standing`: P.N = |V| ≥ 2, every edge weight ≥ 2, 2 ≤ Φ, 0 < ε < 1, 1 ≤ h; reason: these are the section's standing assumptions, restated as hypotheses
--   - generalization: Φ = diam^{(h)}_G(V) → Φ is any real number ≥ 2 (it enters only through k); reason: the proof uses Φ only through the value of k; the paper's Φ = diam^{(h)}_G(V) is ≥ 2 under minimum weight 2 and |V| ≥ 2, so the statement specializes to it
--   - generalization: a call of Algorithm 2 made by Algorithm 1 → any X, M and any scale ∆ > 0 (no call invariant); reason: the argument uses only that radii are ≥ 0 and < k and the choice of centers; it specializes to the calls the algorithm makes
--   - encoding: the output (U, M̂): an HST U with X as leaves and a saved set; the random algorithm → the law (`PMF`) of the pair (d_U, M̂), with d_U : V → V → [0,∞] equal to ∞ off X; recursive calls use independent randomness; loops and recursion carry fuel that is never exhausted under the hypotheses; reason: the statements read U only through d_U; the fuel bounds are reached only by runs the hypotheses exclude (Formalization Notes of the algorithm definitions)
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), Observation 2, p.17 (PDF p.19)

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
Observation 2, p.17 (PDF p.19): "During the ℓ'th phase of the for loop (Line 3 of Algorithm 2), at
most µ_{ℓ−1} balls are carved. Further, every cluster created during the ℓ'th phase contains at most
n/µ_ℓ vertices."

**Formalization Note.** Stated for every final state in the support of the run of Algorithm 2 on
`(G, X, M, h, ∆)`, for every valid center rule, under the standing assumptions of §4 and `∆ > 0`;
`n = |X|`. A ball's phase is recorded in its `Carve` record. -/
theorem observation_2 {V : Type} [Fintype V] [DecidableEq V] (P : Fig2Params) (G : WGraph V) (h : ℕ)
    (rule : CenterRule V) (hS : Standing P G h) (hrule : IsValidRule P G h rule)
    (X M : Finset V) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∀ s ∈ (sspRun P G h rule X M Δ).support, ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ P.L →
      (s.carved.filter fun c => decide (c.phase = ℓ)).length ≤ P.mu (ℓ - 1) ∧
      ∀ c ∈ s.carved, c.phase = ℓ → (c.cluster.card : ℝ) ≤ (X.card : ℝ) / (P.mu ℓ : ℝ) := by sorry

end HopRamsey
