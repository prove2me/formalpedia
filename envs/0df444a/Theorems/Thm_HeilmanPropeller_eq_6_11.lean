-- Prove2me | Theorems.Thm_HeilmanPropeller_eq_6_11
-- name    : HeilmanPropeller.eq_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:13.657199+00:00
-- url     : https://prove2.me/theorems/618abddd-20d5-47c4-8d4a-da719db75f2b
-- title:
--   Display (6.11): $(c-t^2)(L-2t^2)<9t^2$ and $c<t^2+2.15\,t$
-- statement:
--   Throughout, $\gamma_n$ is the standard Gaussian measure on $\mathbb R^n$ (Euclidean norm), and for a partition $\mathcal A=(A_1,\dots,A_k)$ the Gaussian moments, cell measures and value are
--
--   $$z_i=\int_{A_i}x\,d\gamma_n(x),\qquad p_i=\gamma_n(A_i),\qquad F(\mathcal A)=\sum_{i=1}^k\|z_i\|^2 .$$
--
--   $C_k=\sup_{n\ge1}\sup_{\mathcal A}F(\mathcal A)$, the supremum over partitions of $\mathbb R^n$ into $k$ sets (display (1.1)).
--
--   Let $k\ge5$ and let $\mathcal A=(A_1,\dots,A_k)$ be a partition of $\mathbb R^{k-1}$ with $F(\mathcal A)=C_k$ and $\gamma_{k-1}(A_i)>0$ for all $i$, labelled so that $r_1\ge r_2\ge\dots\ge r_k=t$, where $r_i=\|z_i\|/\sqrt{C_k}$. With $L=r_1^2+r_2^2$ and $c=r_3^2$,
--
--   $$(c-t^2)(L-2t^2)<9t^2,\qquad c<t^2+2.15\,t.$$
--
--   These two inequalities on the three largest cells and the smallest one are the input from Section 6 to Lemma 7.1. No partition satisfies these hypotheses: Lemma 7.1 shows $k\le 4$ for every such $\mathcal A$. The statement is a step of that proof by contradiction, and it has this vacuous character in the paper too.
--
--   Differences from the source:
--   - generalization: A is a finite measurable partition of the space → IsPartition A: measurable cells, γ-almost every point in exactly one cell; reason: every exact partition is one, and the statement specializes to exact partitions
--   - encoding: A achieves the supremum C_k (F(A) = C_k) → AchievesCk A: value A ≥ value B for every k-cell IsPartition B of every Space n; reason: a null modification changes no moment, so this is F(A) = C_k with C_k = value A; no real sSup is used
--   - encoding: cells indexed 1, …, k; r₁, r₂, r₃ and the last cell k → Fin k, 0-based: r 0, r 1, r 2 and the cell k − 1; reason: Lean indexing; same instances
-- source:
--   Heilman, On the Propeller Conjecture, arXiv:2610.32158 (held version, sha256 13f5ddf8…), display (6.11), p.13; standing assumptions and notation (6.1), p.11

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HeilmanPropeller_AchievesCk

namespace HeilmanPropeller

open MeasureTheory OAI.GaussianPropeller

/-- **Display (6.11) (constraints on the two largest cells).** Heilman, *On the Propeller
Conjecture*, arXiv:2610.32158 (held version, sha256 13f5ddf8…), display (6.11), p.13, under the
standing assumptions and notation (6.1) of Section 6, p.11.

Let `k ≥ 5` and let `A = (A₁, …, A_k)` be a partition of `ℝ^{k−1}` with `F(A) = C_k` and
`γ_{k−1}(Aᵢ) > 0` for all `i`, labelled so that `r₁ ≥ r₂ ≥ ⋯ ≥ r_k = t`, where `rᵢ = ‖zᵢ‖/√C_k`.
With `L = r₁² + r₂²` and `c = r₃²`,

  `(c − t²)(L − 2t²) < 9t²`  and  `c < t² + 2.15 t`.

**Formalization Note.**
* `AchievesCk A` encodes `F(A) = C_k`, and `C_k = value A`.
* Indices are 0-based: the paper's `r₁, r₂, r₃` are `r 0, r 1, r 2`, and its `r_k` is `r (k − 1)`.
  The ordering is the paper's relabeling, kept as a hypothesis.
* Section 7 shows that no such `A` exists (Lemma 7.1); this display is a step of that proof by
  contradiction, so its hypotheses are, in the end, never met. -/
theorem eq_6_11 (k : ℕ) (hk : 5 ≤ k) (A : Fin k → Set (Space (k - 1))) (hA : AchievesCk A)
    (hpos : ∀ i, 0 < gaussian (k - 1) (A i)) :
    let r : Fin k → ℝ := fun i => ‖centroid (A i)‖ / Real.sqrt (value A)
    let t : ℝ := r ⟨k - 1, by omega⟩
    let L : ℝ := r ⟨0, by omega⟩ ^ 2 + r ⟨1, by omega⟩ ^ 2
    let c : ℝ := r ⟨2, by omega⟩ ^ 2
    (∀ i j : Fin k, i ≤ j → r j ≤ r i) →
    (c - t ^ 2) * (L - 2 * t ^ 2) < 9 * t ^ 2 ∧ c < t ^ 2 + 2.15 * t := by sorry

end HeilmanPropeller
