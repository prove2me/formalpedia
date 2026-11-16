-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_Supplement_lemma_6_8
-- name    : InducedExpanderTest989.Structural.Supplement.lemma_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:32:38.058886+00:00
-- url     : https://prove2.me/theorems/3be369d0-dece-4ff3-bc7b-75549b80c463
-- title:
--   Lemma 6.8 — the planted likelihood ratio on a separated multigraph
-- statement:
--   Let $r\ge1$, $K=\mathbb F_2^r$, $q=2^r$, and let $0\le p\le1/4$ be a noise rate with bias $\rho=1-qp/(q-1)$. Let $H$ be a finite multigraph with a spanning forest $F$ and $R$ nonforest edges, and let $D_{\rm sep}\ge1$ be an integer. Assume that the $2R$ endpoints of the nonforest edges are distinct and pairwise at distance at least $D_{\rm sep}$ in $F$ (distance $\infty$ between different trees). Then every labelling $y\in K^{E(H)}$ satisfies
--   $$|D_H(y)-1|\le\big(1+(q-1)\rho^{D_{\rm sep}}\big)^R-1\le\exp\big((q-1)R\rho^{D_{\rm sep}}\big)-1,$$
--   where $D_H(y)=q^{|E(H)|}\Pr^H_{\mathcal P}(y)$ is the likelihood ratio of the planted noisy-potential law against the uniform law of labels.
--
--   When an algorithm has exposed a forest plus a few far-apart extra edges, its view under the planted law is close to its view under uniform labels. This is the analytic core of the indistinguishability step in the lower bound of Theorem 6.1.
--
--   **Formalization Note** The multigraph is a pair of finite types with an endpoint map, loops and parallel edges allowed. Distinctness of the endpoints is injectivity of the map from (nonforest edge, side) to vertices. Both inequalities are conclusions.
--
--   Differences from the source:
--   - encoding: a finite multigraph H with spanning forest F and nonforest edges → finite types V, E, ends : E → V × V and F : Finset E with IsSpanningForest; R = |E \ F|; reason: Lean representation of the same objects
--   - encoding: the 2R endpoints of the nonforest edges are distinct → the endpoint-occurrence map on (E \ F) × Fin 2 is injective; reason: the same condition
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.41 (PDF p.43), Lemma 6.8, eq. (35); objects pp.35–37, 40 (PDF pp.37–39, 42), eqs. (23), (34)

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Supplement_NoisyLabels

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural.Supplement

/-- Peng–Shen, STOC 2027 #989, Lemma 6.8 (p. 41, PDF 43), both inequalities of (35). `H` is the
finite multigraph `(V, E, ends)`, `R = |E \ F|`, `q = 2^r`, `ρ = noiseBias r p`. -/
theorem lemma_6_8 {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (r : ℕ) (hr : 1 ≤ r) (ends : E → V × V) (F : Finset E) (hF : IsSpanningForest ends F)
    (Dsep : ℕ) (hD : 1 ≤ Dsep)
    (hdistinct : Function.Injective (nonforestEndpoint ends F))
    (hsep : ∀ a b : {e // e ∉ F} × Fin 2, a ≠ b →
      (Dsep : ℕ∞) ≤ forestDist ends F (nonforestEndpoint ends F a) (nonforestEndpoint ends F b))
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1/4) (y : E → LabelGroup r) :
    |likelihoodRatio r p ends y - 1| ≤
        (1 + ((2 : ℝ) ^ r - 1) * noiseBias r p ^ Dsep) ^ (Finset.univ \ F).card - 1 ∧
      (1 + ((2 : ℝ) ^ r - 1) * noiseBias r p ^ Dsep) ^ (Finset.univ \ F).card - 1 ≤
        Real.exp (((2 : ℝ) ^ r - 1) * (Finset.univ \ F).card * noiseBias r p ^ Dsep) - 1 := by sorry

end InducedExpanderTest989.Structural.Supplement
