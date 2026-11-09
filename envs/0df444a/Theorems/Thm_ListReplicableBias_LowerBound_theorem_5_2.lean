-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_theorem_5_2
-- name    : ListReplicableBias.LowerBound.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:32.934765+00:00
-- url     : https://prove2.me/theorems/d909d7ea-1dfc-43e6-8961-e15cf7efbfba
-- title:
--   Theorem 5.2 — Neighborhood Sperner/KKM Lemma
-- statement:
--   Let $d\in\mathbb N$, $a<b$, $s=b-a$, and let $\chi:[a,b]^d\to C$ be any Sperner/KKM coloring, with arbitrary color set $C$. For every $0<r\le s/2$ there exist $p\in[a,b]^d$ and finitely many points $T\subseteq[a,b]^d\cap B^\circ_\infty(r,p)$ with pairwise different colors such that
--   $$|T|\ge\left(1+\frac23\frac r s\right)^d.$$
--   This is the cited geometric input to the lower bound. No regularity of the coloring is assumed.
--
--   Differences from the source:
--   - encoding: $\mathbb R^d$ with $\ell_\infty$ distance → functions on `Fin d` with their sup norm; reason: this reindexes the same finite coordinates and preserves every distance
--   - encoding: a coloring defined on the cube → an ambient coloring restricted to cube points; reason: every cube coloring extends to the ambient space by choosing a cube point for the values outside, so no cube coloring is lost
--   - encoding: at least a real number of points with distinct colors → a finite witness set with injective coloring and a real cardinality bound; reason: an infinite color set contains finite subsets of every required finite size, and a finite color set satisfies the same bound
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Theorem 5.2, PDF p. 4

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_ListReplicability

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound

/-- Theorem 5.2 [VWDP+24], PDF p. 4. Finite witnesses express the real lower
bound without assigning cardinality zero to an infinite color set. -/
theorem theorem_5_2 {d : ℕ} {C : Type*} (a b r : ℝ)
    (χ : (Fin d → ℝ) → C) (hab : a < b)
    (hχ : IsSpernerKKMColoring a b χ) (hr : 0 < r) (hrs : r ≤ (b - a) / 2) :
    ∃ p ∈ cube d a b, ∃ T : Finset (Fin d → ℝ),
      (∀ q ∈ T, q ∈ cube d a b ∩ openBall p r) ∧
      Set.InjOn χ (T : Set (Fin d → ℝ)) ∧
      (1 + (2 / 3 : ℝ) * (r / (b - a))) ^ d ≤ (T.card : ℝ) := by sorry

end ListReplicableBias.LowerBound
