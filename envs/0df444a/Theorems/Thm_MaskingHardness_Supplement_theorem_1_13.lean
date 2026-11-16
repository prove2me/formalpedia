-- Prove2me | Theorems.Thm_MaskingHardness_Supplement_theorem_1_13
-- name    : MaskingHardness.Supplement.theorem_1_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:34:35.720451+00:00
-- url     : https://prove2.me/theorems/68c22826-f9f3-4f0a-8b63-506fe5fd7901
-- title:
--   Theorem 1.13 — Crammer–Singer hinge loss vs maximum TV distance
-- statement:
--   For all finite $\mathcal X$ and $\mathcal Y=[k]$, distributions over $(x,y)\in\mathcal X\times\mathcal Y$, finite $\mathcal C\subseteq\{\mathcal X\to\mathbb R^k\}$ and $\varepsilon>0$,
--
--   $$
--   \min_{\lambda\in\mathbb R^{\mathcal C}}\ \mathbb E\big[\ell_{\mathrm{CS}}(y,c_\lambda(x))\big]+\varepsilon\|\lambda\|_1\ =\ \max_{p:\mathcal X\times\mathcal Y\to\Delta_k}\mathbb E\big[d_{\mathrm{TV}}(y,p(x,y))\big]\quad\text{s.t. }\forall c\in\mathcal C,\ \Big|\mathbb E\big[\langle c(x),\,y-p(x,y)\rangle\big]\Big|\le\varepsilon,
--   $$
--
--   with both optima attained. Here $\ell_{\mathrm{CS}}$ is the Crammer–Singer hinge loss (Definition 5.1) and $d_{\mathrm{TV}}(y,z)$ is the total variation distance of $z$ from the point mass at the label $y$.
--
--   The right side is the largest statistical distance of modified labels $p(x,y)$ that remain computationally indistinguishable from the original labels; the distance is measured from the point mass $y$, so it depends on the coupling between original and modified labels.
--
--   **Formalization Note** $\ell_{\mathrm{CS}}$ is written in a total form that equals $0$ when $k=1$, where the maximum over wrong labels is empty. $d_{\mathrm{TV}}(y,z)=\tfrac12\sum_j|(e_y)_j-z_j|$ is the published total variation distance `HybridXorLift.tvDist` applied to $e_y$ and $z$.
--
--   Differences from the source:
--   - encoding: labels y ∈ Y = [k] as one-hot vectors e_y → y : Fin k, with e_y = Pi.single y 1 (or [j = y] entrywise); reason: the identification of p.4
--   - encoding: a distribution over (x, y) ∈ X × Y → weights D x y with IsDist D (nonnegative, summing to 1), expectations as weighted finite sums; reason: the same distributions; zero-probability pairs allowed
--   - encoding: a finite class C ⊆ {X → ℝᵏ} and c_λ = ∑_{c∈C} λ_c c → a finite indexed family c : ι → X → ℝᵏ with c_λ = combo c λ; reason: an indexed family with ι = C recovers the set; repeated members change neither side, since splitting a coefficient among copies never lowers ε‖λ‖₁ and the constraints repeat
--   - encoding: min_λ … = max … (both sides attained) → ∃ v : ℝ, IsLeast of the range of the left objective and IsGreatest of the set of feasible right values; reason: "min" and "max" assert attainment; one common value v says the two optima are equal
--   - encoding: ℓCS(e_i, a) = (1 − a_i + max_{j≠i} a_j)₊ with the empty max −∞ at k = 1 → lossCS i a = 1 − ã_i + max_j (ã_j − [j = i]), ã = π(a); reason: equal for k ≥ 2 and both 0 at k = 1; ℓCS is invariant under constant shifts, so centering changes nothing
--   - encoding: d_TV(y, p(x, y)), the TV distance from the point mass at y → HybridXorLift.tvDist (Pi.single y 1) (p x y) = ½ ∑_j |(e_y)_j − p(x,y)_j|; reason: the published TV distance ½∑|P − P′| of two vectors on a finite set, applied to e_y
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 1.13, p.8 (PDF p.10); restated with proof pp.25–26 (PDF pp.27–28)

import Mathlib
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_combo
import Definitions.Def_MaskingHardness_Supplement_lossCS
import Definitions.Def_HybridXorLift_tvDist

namespace MaskingHardness.Supplement

/-- **Theorem 1.13** (Crammer–Singer Hinge Loss vs Maximum TV Distance) (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Theorem 1.13,
printed p.8 = PDF p.10; restated with proof printed pp.25–26 = PDF pp.27–28).

For all finite `X` and `Y = [k]`, distributions over `(x, y) ∈ X × Y`, finite `C ⊆ {X → ℝᵏ}` and
`ε > 0`,
`min_λ E[ℓCS(y, c_λ(x))] + ε‖λ‖₁ = max_{p : X×Y→Δ_k} E[d_TV(y, p(x, y))]` s.t.
`∀ c ∈ C, |E[⟨c(x), y − p(x, y)⟩]| ≤ ε`.

**Formalization Note** `ℓCS` is `lossCS` (total form, `0` when `k = 1`, see its definition);
`d_TV(y, z) = ½∑_j |(e_y)_j − z_j|` is the published `HybridXorLift.tvDist` (total variation
distance `½ ∑ |P − P′|` of two vectors on a finite set) applied to `e_y = Pi.single y 1` and `z`; `p` depends on `(x, y)`. "min = max" is one real
`v` that is `IsLeast`/`IsGreatest` on the two sides. -/
theorem theorem_1_13 {X ι : Type*} [Fintype X] [Fintype ι] {k : ℕ}
    (D : X → Fin k → ℝ) (hD : IsDist D) (c : ι → X → Fin k → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : ℝ,
      IsLeast (Set.range fun lam : ι → ℝ =>
          ∑ x, ∑ y, D x y * lossCS y (combo c lam x) + ε * ∑ i, |lam i|) v ∧
      IsGreatest {u : ℝ | ∃ p : X → Fin k → Fin k → ℝ,
          (∀ x y, p x y ∈ stdSimplex ℝ (Fin k)) ∧
          (∀ i, |∑ x, ∑ y, D x y * (c i x ⬝ᵥ ((Pi.single y (1 : ℝ) : Fin k → ℝ) - p x y))| ≤ ε) ∧
          u = ∑ x, ∑ y, D x y *
            HybridXorLift.tvDist (Pi.single y (1 : ℝ) : Fin k → ℝ) (p x y)} v := by sorry

end MaskingHardness.Supplement
