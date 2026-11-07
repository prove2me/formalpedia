-- Prove2me | Theorems.Thm_HeilmanPropeller_lemma_5_2
-- name    : HeilmanPropeller.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:15.860212+00:00
-- url     : https://prove2.me/theorems/eaf39ed8-9f51-4795-8039-eb4d970541c5
-- title:
--   Lemma 5.2: $p_i\ge 0.415\,r_i+0.15\,r_i^2$
-- statement:
--   Throughout, $\gamma_n$ is the standard Gaussian measure on $\mathbb R^n$ (Euclidean norm), and for a partition $\mathcal A=(A_1,\dots,A_k)$ the Gaussian moments, cell measures and value are
--
--   $$z_i=\int_{A_i}x\,d\gamma_n(x),\qquad p_i=\gamma_n(A_i),\qquad F(\mathcal A)=\sum_{i=1}^k\|z_i\|^2 .$$
--
--   $C_k=\sup_{n\ge1}\sup_{\mathcal A}F(\mathcal A)$, the supremum over partitions of $\mathbb R^n$ into $k$ sets (display (1.1)).
--
--   Let $k\ge5$ and let $\mathcal A=(A_1,\dots,A_k)\subseteq\mathbb R^{k-1}$ achieve the supremum in the definition of $C_k$, with $\gamma_{k-1}(A_i)>0$ for all $i$. With $r_i=\|z_i\|/\sqrt{C_k}$,
--
--   $$p_i\ge 0.415\,r_i+0.15\,r_i^2\qquad\text{for all }1\le i\le k.$$
--
--   This constraint feeds Lemma 7.1. No partition satisfies these hypotheses: Lemma 7.1 shows $k\le 4$ for every such $\mathcal A$. The statement is a step of that proof by contradiction, and it has this vacuous character in the paper too.
--
--   Differences from the source:
--   - generalization: A is a finite measurable partition of the space → IsPartition A: measurable cells, γ-almost every point in exactly one cell; reason: every exact partition is one, and the statement specializes to exact partitions
--   - encoding: A achieves the supremum C_k (F(A) = C_k) → AchievesCk A: value A ≥ value B for every k-cell IsPartition B of every Space n; reason: a null modification changes no moment, so this is F(A) = C_k with C_k = value A; no real sSup is used
-- source:
--   Heilman, On the Propeller Conjecture, arXiv:2610.32158 (held version, sha256 13f5ddf8…), Lemma 5.2, p.9, display (5.7); notation (5.1), p.8

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HeilmanPropeller_AchievesCk

namespace HeilmanPropeller

open MeasureTheory OAI.GaussianPropeller

/-- **Lemma 5.2 (more constraints).** Heilman, *On the Propeller Conjecture*, arXiv:2610.32158
(held version, sha256 13f5ddf8…), Lemma 5.2, p.9, display (5.7), with the notation (5.1), p.8.

Let `k ≥ 5` and let `A = (A₁, …, A_k) ⊆ ℝ^{k−1}` achieve the supremum in the definition of `C_k`,
with `γ_{k−1}(Aᵢ) > 0` for all `i`. With `rᵢ = ‖zᵢ‖/√C_k` and `pᵢ = γ_{k−1}(Aᵢ)`,
`pᵢ ≥ 0.415 rᵢ + 0.15 rᵢ²` for all `i`.

**Formalization Note.** `AchievesCk A` encodes "achieves the supremum", and then `C_k = value A`.
Section 7 shows that no such `A` exists (Lemma 7.1); this lemma is a step of that proof by
contradiction, so its hypotheses are, in the end, never met. -/
theorem lemma_5_2 (k : ℕ) (hk : 5 ≤ k) (A : Fin k → Set (Space (k - 1))) (hA : AchievesCk A)
    (hpos : ∀ i, 0 < gaussian (k - 1) (A i)) :
    let r : Fin k → ℝ := fun i => ‖centroid (A i)‖ / Real.sqrt (value A)
    ∀ i, 0.415 * r i + 0.15 * r i ^ 2 ≤ (gaussian (k - 1)).real (A i) := by sorry

end HeilmanPropeller
