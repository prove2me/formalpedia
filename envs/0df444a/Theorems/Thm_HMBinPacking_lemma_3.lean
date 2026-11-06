-- Prove2me | Theorems.Thm_HMBinPacking_lemma_3
-- name    : HMBinPacking.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:58:33.188979+00:00
-- url     : https://prove2.me/theorems/f9baaf13-6831-42f6-af60-fa7e593fb1b1
-- title:
--   Lemma 3 — Carathéodory's theorem for $t\,\mathrm{conv}(V)$ with $d+1$ points
-- statement:
--   Let $V\subseteq\mathbb R^d$ be finite and nonempty, let $t>0$, and let $z\in t\,\mathrm{conv}(V)$. Then there exist points $v_1,\dots,v_{d+1}\in V$ and nonnegative reals $\alpha_1,\dots,\alpha_{d+1}$ such that
--   $$
--   z=\sum_{i=1}^{d+1}\alpha_i v_i,\qquad \sum_{i=1}^{d+1}\alpha_i=t .
--   $$
--
--   The dimension $d$ is arbitrary here (it is not the number of item sizes). This is the form of Carathéodory's theorem used in the proof of Lemma 2.
--
--   Differences from the source: none.
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, Lemma 3 (Carathéodory's theorem; [Roc70], Theorem 17.1), p.4

import Mathlib
open scoped Pointwise

namespace HMBinPacking

/-- **Lemma 3: Carathéodory's theorem for `t conv(V)`.**
Koana, Kumabe, arXiv:2609.16923v2, Lemma 3, p.4: "Lemma 3 (Carathéodory’s theorem; [Roc70],
Theorem 17.1). Let V ⊆ R^d be finite and nonempty, let t > 0, and let z ∈ t conv(V). There exist
points v1, . . . , v_{d+1} ∈ V and nonnegative real numbers α1, . . . , α_{d+1} such that
z = ∑_{i=1}^{d+1} αi vi and ∑_{i=1}^{d+1} αi = t."

**Formalization Note.** `R^d` is `Fin d → ℝ` for an arbitrary dimension `d` (not the instance's
`d`); `t conv(V)` is the pointwise dilation `t • convexHull ℝ V`. The `d + 1` points are a family
`v : Fin (d + 1) → V`; repetitions are allowed, as in the statement. -/
theorem lemma_3 {d : ℕ} (V : Set (Fin d → ℝ)) (hVfin : V.Finite) (hVne : V.Nonempty) (t : ℝ)
    (ht : 0 < t) (z : Fin d → ℝ) (hz : z ∈ t • convexHull ℝ V) :
    ∃ (v : Fin (d + 1) → Fin d → ℝ) (α : Fin (d + 1) → ℝ),
      (∀ i, v i ∈ V) ∧ (∀ i, 0 ≤ α i) ∧ z = ∑ i, α i • v i ∧ ∑ i, α i = t := by sorry

end HMBinPacking
