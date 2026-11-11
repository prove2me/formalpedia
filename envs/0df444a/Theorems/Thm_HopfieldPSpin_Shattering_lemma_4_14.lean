-- Prove2me | Theorems.Thm_HopfieldPSpin_Shattering_lemma_4_14
-- name    : HopfieldPSpin.Shattering.lemma_4_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:09:46.99943+00:00
-- url     : https://prove2.me/theorems/c0cfff28-834e-4f47-bd9e-d785713a0e61
-- title:
--   Lemma 4.14 — gap-free sets split into clusters of diameter $<rn$, size $\le(n+1)e^{nh(r)}$, separation $>Rn$
-- statement:
--   Let $0<2r<R<1/2$ and let $S\subseteq\Sigma_n$ satisfy $d_n(\sigma,\tau)\notin[r,R]$ for all distinct $\sigma,\tau\in S$. Let $G_r(S)$ be the graph on $S$ with an edge $\{\sigma,\tau\}$ when $\sigma\ne\tau$ and $d_H(\sigma,\tau)<rn$. Then the vertex set $C$ of any connected component of $G_r(S)$ satisfies
--   $$\operatorname{diam}_H(C)<rn,\qquad |C|\le(n+1)e^{nh(r)},$$
--   and any two distinct components $C,C'$ satisfy $\operatorname{dist}_H(C,C')>Rn$.
--
--   It turns the absence of intermediate distances into the cluster decomposition of Definition 2.1.
--
--   Differences from the source:
--   - encoding: spins $\sigma\in\{-1,1\}^n$, patterns $k=1,\dots,M$, coordinates $i=1,\dots,n$ → `Config n = Fin n → ℤˣ` (the units of ℤ are exactly ±1), patterns `Fin M`, coordinates `Fin n` (0-based); reason: Lean convention; the same configurations and indices
--   - generalization: standing $n\ge p\ge3$ → `1 ≤ n`; reason: the lemma does not involve $p$; every $n\ge p\ge3$ satisfies $n\ge1$ (at $n=0$ the strict diameter bound fails)
--   - encoding: connected components of $G_r(S)$ as vertex sets → Mathlib `SimpleGraph.ConnectedComponent` of a graph on the subtype $S$, mapped to a `Finset` of configurations; reason: same components
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 33 (PDF 35), Lemma 4.14

import Mathlib
import Definitions.Def_HopfieldPSpin_Shattering_Model
import Definitions.Def_HopfieldPSpin_Shattering_Shattered

namespace HopfieldPSpin.Shattering

/-- Lemma 4.14 (p. 33): if `0 < 2r < R < 1/2` and no two distinct points of `S ⊆ Σ_n` are at
normalized distance in `[r, R]`, then every connected component `C` of `G_r(S)` has
`diam_H(C) < r n` and `|C| ≤ (n + 1) e^{n h(r)}`, and distinct components are at Hamming
distance `> R n`. -/
theorem lemma_4_14 (n : ℕ) (hn : 1 ≤ n) (r R : ℝ) (hr : 0 < 2 * r) (hrR : 2 * r < R)
    (hR : R < 1 / 2) (S : Finset (Config n))
    (hS : ∀ σ ∈ S, ∀ τ ∈ S, σ ≠ τ → ¬ (r ≤ normDist σ τ ∧ normDist σ τ ≤ R)) :
    (∀ C : (clusterGraph n r S).ConnectedComponent,
      (diamH (componentVerts C) : ℝ) < r * n ∧
      ((componentVerts C).card : ℝ) ≤ ((n : ℝ) + 1) * Real.exp (n * Real.binEntropy r)) ∧
    ∀ C C' : (clusterGraph n r S).ConnectedComponent, C ≠ C' →
      R * n < (distH (componentVerts C) (componentVerts C') : ℝ) := by sorry

end HopfieldPSpin.Shattering
