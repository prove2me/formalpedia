-- Prove2me | Theorems.Thm_MaskingHardness_Supplement_theorem_1_12
-- name    : MaskingHardness.Supplement.theorem_1_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:34:06.483858+00:00
-- url     : https://prove2.me/theorems/ccf41d9b-60b1-46b1-8910-d10c595f32d0
-- title:
--   Theorem 1.12 — strong hinge loss vs arbitrary noise
-- statement:
--   For all finite $\mathcal X$ and $\mathcal Y=[k]$, distributions over $(x,y)\in\mathcal X\times\mathcal Y$, finite $\mathcal C\subseteq\{\mathcal X\to\mathbb R^k\}$ and $\varepsilon>0$,
--
--   $$
--   \min_{\lambda\in\mathbb R^{\mathcal C}}\ \mathbb E\big[\ell_{\mathrm{strong}}(y,\pi(c_\lambda(x)))\big]+\varepsilon\|\lambda\|_1\ =\ \max_{W:\mathcal X\to\Delta_k^k}\mathbb E\big[\langle y,W(x)y\rangle\big]\quad\text{s.t. }\forall c\in\mathcal C,\ \Big|\mathbb E\big[\langle c(x),\,W(x)y-\vec1/k\rangle\big]\Big|\le\varepsilon,
--   $$
--
--   with both optima attained. Here $\pi$ is the centering map and $\ell_{\mathrm{strong}}$ the strong hinge loss (Definition 5.1).
--
--   The right side is the largest fidelity $\mathbb E[\langle y,W(x)y\rangle]=1-\mathbb E[d_{\mathrm{TV}}(y,W(x)y)]$ of a $(\mathcal C,\varepsilon)$-masking channel: the least amount of arbitrary (not necessarily uniform) noise that makes the labels indistinguishable from uniform.
--
--   **Formalization Note** The left objective is the published `lossObjective` with $g=\ell_{\mathrm{strong}}$ and the constraint is the published `IsMaskingChannel`.
--
--   Differences from the source:
--   - encoding: labels y ∈ Y = [k] as one-hot vectors e_y → y : Fin k, with e_y = Pi.single y 1 (or [j = y] entrywise); reason: the identification of p.4
--   - encoding: a distribution over (x, y) ∈ X × Y → weights D x y with IsDist D (nonnegative, summing to 1), expectations as weighted finite sums; reason: the same distributions; zero-probability pairs allowed
--   - encoding: a finite class C ⊆ {X → ℝᵏ} and c_λ = ∑_{c∈C} λ_c c → a finite indexed family c : ι → X → ℝᵏ with c_λ = combo c λ; reason: an indexed family with ι = C recovers the set; repeated members change neither side, since splitting a coefficient among copies never lowers ε‖λ‖₁ and the constraints repeat
--   - encoding: min_λ … = max … (both sides attained) → ∃ v : ℝ, IsLeast of the range of the left objective and IsGreatest of the set of feasible right values; reason: "min" and "max" assert attainment; one common value v says the two optima are equal
--   - encoding: ⟨y, W(x)y⟩ → W x y y, the y-th entry of column y of W(x); reason: W(x)y is column y of W(x) and y is the one-hot e_y
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 1.12, p.8 (PDF p.10); restated with proof p.25 (PDF p.27)

import Mathlib
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_IsMaskingChannel
import Definitions.Def_MaskingHardness_lossObjective
import Definitions.Def_MaskingHardness_Supplement_lossStrong

namespace MaskingHardness.Supplement

/-- **Theorem 1.12** (Strong Hinge Loss vs Arbitrary Noise) (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Theorem 1.12, printed p.8 = PDF
p.10; restated with proof printed p.25 = PDF p.27).

For all finite `X` and `Y = [k]`, distributions over `(x, y) ∈ X × Y`, finite `C ⊆ {X → ℝᵏ}` and
`ε > 0`,
`min_λ E[ℓstrong(y, π(c_λ(x)))] + ε‖λ‖₁ = max_{W : X → Δ_k^k} E[⟨y, W(x)y⟩]` s.t.
`∀ c ∈ C, |E[⟨c(x), W(x)y − 1⃗/k⟩]| ≤ ε`.

**Formalization Note** The left objective is the published `lossObjective D c lossStrong ε`,
which applies `ℓstrong` to `π(c_λ(x))` (`ℓstrong` itself also centers, and centering is
idempotent). The constraint together with `W : X → Δ_k^k` is the published `IsMaskingChannel`.
`⟨y, W(x)y⟩` is the `y`-th entry of column `y` of `W(x)`, i.e. `W x y y`. "min = max" is one
real `v` that is `IsLeast`/`IsGreatest` on the two sides. -/
theorem theorem_1_12 {X ι : Type*} [Fintype X] [Fintype ι] {k : ℕ}
    (D : X → Fin k → ℝ) (hD : IsDist D) (c : ι → X → Fin k → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : ℝ,
      IsLeast (Set.range (lossObjective D c (fun y a => lossStrong y a) ε)) v ∧
      IsGreatest {u : ℝ | ∃ W : X → Matrix (Fin k) (Fin k) ℝ,
          IsMaskingChannel D c ε W ∧ u = ∑ x, ∑ y, D x y * W x y y} v := by sorry

end MaskingHardness.Supplement
