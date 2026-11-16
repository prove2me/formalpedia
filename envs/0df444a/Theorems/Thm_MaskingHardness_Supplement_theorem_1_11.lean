-- Prove2me | Theorems.Thm_MaskingHardness_Supplement_theorem_1_11
-- name    : MaskingHardness.Supplement.theorem_1_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:33:31.358193+00:00
-- url     : https://prove2.me/theorems/8a3a8b5e-f3f2-409f-b5be-0e09159e5ee7
-- title:
--   Theorem 1.11 — weak hinge loss vs uniform noise
-- statement:
--   For all finite $\mathcal X$ and $\mathcal Y=[k]$, distributions over $(x,y)\in\mathcal X\times\mathcal Y$, finite $\mathcal C\subseteq\{\mathcal X\to\mathbb R^k\}$ and $\varepsilon>0$,
--
--   $$
--   \min_{\lambda\in\mathbb R^{\mathcal C}}\ \mathbb E\big[\ell_{\mathrm{weak}}(y,c_\lambda(x))\big]+\varepsilon\|\lambda\|_1\ =\ \max_{\mu:\mathcal X\times\mathcal Y\to[0,1]}\mathbb E[\mu(x,y)]\quad\text{s.t. }\forall c\in\mathcal C,\ \Big|\mathbb E\big[\mu(x,y)\,\langle c(x),\,y-\vec1/k\rangle\big]\Big|\le\varepsilon,
--   $$
--
--   with both optima attained. Here labels are one-hot vectors and $\ell_{\mathrm{weak}}$ is the weak hinge loss (Definition 5.1), which centers its action.
--
--   The right side is the largest density of a measure $\mu$ such that the noisy channel outputting $\mu(x,y)\,y+(1-\mu(x,y))\vec1/k$ is $(\mathcal C,\varepsilon)$-masking: hardness under $\ell_{\mathrm{weak}}$ is exactly the existence of a dense measure masking the labels with uniform noise.
--
--   Differences from the source:
--   - encoding: labels y ∈ Y = [k] as one-hot vectors e_y → y : Fin k, with e_y = Pi.single y 1 (or [j = y] entrywise); reason: the identification of p.4
--   - encoding: a distribution over (x, y) ∈ X × Y → weights D x y with IsDist D (nonnegative, summing to 1), expectations as weighted finite sums; reason: the same distributions; zero-probability pairs allowed
--   - encoding: a finite class C ⊆ {X → ℝᵏ} and c_λ = ∑_{c∈C} λ_c c → a finite indexed family c : ι → X → ℝᵏ with c_λ = combo c λ; reason: an indexed family with ι = C recovers the set; repeated members change neither side, since splitting a coefficient among copies never lowers ε‖λ‖₁ and the constraints repeat
--   - encoding: min_λ … = max … (both sides attained) → ∃ v : ℝ, IsLeast of the range of the left objective and IsGreatest of the set of feasible right values; reason: "min" and "max" assert attainment; one common value v says the two optima are equal
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 1.11, p.7 (PDF p.9); restated with proof p.25 (PDF p.27)

import Mathlib
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_combo
import Definitions.Def_MaskingHardness_Supplement_lossWeak

namespace MaskingHardness.Supplement

/-- **Theorem 1.11** (Weak Hinge Loss vs Uniform Noise) (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Theorem 1.11, printed p.7 = PDF
p.9; restated with proof printed p.25 = PDF p.27).

For all finite `X` and `Y = [k]`, distributions over `(x, y) ∈ X × Y`, finite `C ⊆ {X → ℝᵏ}` and
`ε > 0`,
`min_λ E[ℓweak(y, c_λ(x))] + ε‖λ‖₁ = max_{µ : X×Y→[0,1]} E[µ(x, y)]` s.t.
`∀ c ∈ C, |E[µ(x, y)⟨c(x), y − 1⃗/k⟩]| ≤ ε`.

**Formalization Note** "min = max" is one real `v` that is `IsLeast` of the range of the left
objective and `IsGreatest` of the set of feasible right values. Labels are `Fin k` with
`y = Pi.single y 1`; `c_λ` is the published `combo`; `ℓweak` centers its action first
(Definition 5.1), so no `π` is applied outside it; `1⃗/k` is the constant vector `(k : ℝ)⁻¹`. -/
theorem theorem_1_11 {X ι : Type*} [Fintype X] [Fintype ι] {k : ℕ}
    (D : X → Fin k → ℝ) (hD : IsDist D) (c : ι → X → Fin k → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : ℝ,
      IsLeast (Set.range fun lam : ι → ℝ =>
          ∑ x, ∑ y, D x y * lossWeak y (combo c lam x) + ε * ∑ i, |lam i|) v ∧
      IsGreatest {u : ℝ | ∃ μ : X → Fin k → ℝ, (∀ x y, μ x y ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ i, |∑ x, ∑ y, D x y *
            (μ x y * (c i x ⬝ᵥ ((Pi.single y (1 : ℝ) : Fin k → ℝ) - fun _ => (k : ℝ)⁻¹)))| ≤ ε) ∧
          u = ∑ x, ∑ y, D x y * μ x y} v := by sorry

end MaskingHardness.Supplement
