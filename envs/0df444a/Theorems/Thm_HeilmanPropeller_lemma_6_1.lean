-- Prove2me | Theorems.Thm_HeilmanPropeller_lemma_6_1
-- name    : HeilmanPropeller.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:13.757086+00:00
-- url     : https://prove2.me/theorems/895b2138-d3c0-437e-8b87-8ce37b00e82b
-- title:
--   Lemma 6.1: two competing scores
-- statement:
--   Throughout, $\gamma_n$ is the standard Gaussian measure on $\mathbb R^n$ (Euclidean norm), and for a partition $\mathcal A=(A_1,\dots,A_k)$ the Gaussian moments, cell measures and value are
--
--   $$z_i=\int_{A_i}x\,d\gamma_n(x),\qquad p_i=\gamma_n(A_i),\qquad F(\mathcal A)=\sum_{i=1}^k\|z_i\|^2 .$$
--
--   $C_k=\sup_{n\ge1}\sup_{\mathcal A}F(\mathcal A)$, the supremum over partitions of $\mathbb R^n$ into $k$ sets (display (1.1)).
--
--   Let $k\ge5$ and let $\mathcal A=(A_1,\dots,A_k)$ be a partition of $\mathbb R^{k-1}$ with $F(\mathcal A)=C_k$ and $\gamma_{k-1}(A_i)>0$ for all $i$, labelled so that $r_1\ge r_2\ge\dots\ge r_k=t$, where $r_i=\|z_i\|/\sqrt{C_k}$. Put, for $j,\ell<k$,
--
--   $$\alpha_j=-\frac{\langle z_k,z_j\rangle}{\|z_k\|^2},\qquad H_{j\ell}=\frac{\langle z_j,z_\ell\rangle}{C_k}-\alpha_j\alpha_\ell t^2,\qquad h_j=H_{jj},\qquad D_{j\ell}=\sqrt{h_jh_\ell-H_{j\ell}^2}.$$
--
--   Then for every pair of distinct indices $j,\ell<k$,
--
--   $$D_{j\ell}\le\frac3\pi\,t\,(1+\alpha_j)(1+\alpha_\ell).$$
--
--   $H$ is the covariance of the residual scores $Y_j$ (6.3)–(6.4) and $D_{j\ell}$ is the square root of a $2\times2$ minor. No partition satisfies these hypotheses: Lemma 7.1 shows $k\le 4$ for every such $\mathcal A$. The statement is a step of that proof by contradiction, and it has this vacuous character in the paper too.
--
--   Differences from the source:
--   - generalization: A is a finite measurable partition of the space → IsPartition A: measurable cells, γ-almost every point in exactly one cell; reason: every exact partition is one, and the statement specializes to exact partitions
--   - encoding: A achieves the supremum C_k (F(A) = C_k) → AchievesCk A: value A ≥ value B for every k-cell IsPartition B of every Space n; reason: a null modification changes no moment, so this is F(A) = C_k with C_k = value A; no real sSup is used
--   - encoding: cells indexed 1, …, k; r₁, r₂, r₃ and the last cell k → Fin k, 0-based: r 0, r 1, r 2 and the cell k − 1; reason: Lean indexing; same instances
-- source:
--   Heilman, On the Propeller Conjecture, arXiv:2610.32158 (held version, sha256 13f5ddf8…), Lemma 6.1, display (6.6), p.12; standing assumptions and notation (6.1)–(6.5), pp.11–12

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HeilmanPropeller_AchievesCk

namespace HeilmanPropeller

open MeasureTheory OAI.GaussianPropeller
open scoped RealInnerProductSpace

/-- **Lemma 6.1 (two competing scores).** Heilman, *On the Propeller Conjecture*,
arXiv:2610.32158 (held version, sha256 13f5ddf8…), Lemma 6.1, display (6.6), p.12, under the
standing assumptions and notation of Section 6, displays (6.1)–(6.5), pp.11–12.

Let `k ≥ 5` and let `A = (A₁, …, A_k)` be a partition of `ℝ^{k−1}` with `F(A) = C_k` and
`γ_{k−1}(Aᵢ) > 0` for all `i`, labelled so that `r₁ ≥ r₂ ≥ ⋯ ≥ r_k = t`, where `rᵢ = ‖zᵢ‖/√C_k`.
Put `αⱼ = −⟨z_k, zⱼ⟩/‖z_k‖²`, `H_{jℓ} = ⟨zⱼ, z_ℓ⟩/C_k − αⱼα_ℓ t²`, `hⱼ = H_{jj}` and
`D_{jℓ} = √(hⱼh_ℓ − H_{jℓ}²)`. Then for every pair of distinct indices `j, ℓ < k`,

  `D_{jℓ} ≤ (3/π) t (1 + αⱼ)(1 + α_ℓ)`.

**Formalization Note.**
* `AchievesCk A` encodes `F(A) = C_k`, and `C_k = value A`.
* Indices are 0-based: the paper's cell `k` (smallest centroid norm) is `last = k − 1`, and
  "`j, ℓ < k`" is `j, ℓ ≠ last`. The ordering `r₁ ≥ ⋯ ≥ r_k` is the paper's relabeling, kept as a
  hypothesis.
* Section 7 shows that no such `A` exists (Lemma 7.1); this lemma is a step of that proof by
  contradiction, so its hypotheses are, in the end, never met. -/
theorem lemma_6_1 (k : ℕ) (hk : 5 ≤ k) (A : Fin k → Set (Space (k - 1))) (hA : AchievesCk A)
    (hpos : ∀ i, 0 < gaussian (k - 1) (A i)) :
    let C : ℝ := value A
    let z : Fin k → Space (k - 1) := fun i => centroid (A i)
    let r : Fin k → ℝ := fun i => ‖z i‖ / Real.sqrt C
    let last : Fin k := ⟨k - 1, by omega⟩
    let t : ℝ := r last
    let α : Fin k → ℝ := fun j => -⟪z last, z j⟫ / ‖z last‖ ^ 2
    let H : Fin k → Fin k → ℝ := fun j l => ⟪z j, z l⟫ / C - α j * α l * t ^ 2
    let h : Fin k → ℝ := fun j => H j j
    let D : Fin k → Fin k → ℝ := fun j l => Real.sqrt (h j * h l - H j l ^ 2)
    (∀ i j : Fin k, i ≤ j → r j ≤ r i) →
    ∀ j l : Fin k, j ≠ l → j ≠ last → l ≠ last →
      D j l ≤ 3 / Real.pi * t * (1 + α j) * (1 + α l) := by sorry

end HeilmanPropeller
