-- Prove2me | Theorems.Thm_MaskingHardness_Supplement_theorem_5_5
-- name    : MaskingHardness.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:36:59.217215+00:00
-- url     : https://prove2.me/theorems/e3867e67-1b05-43af-bbb7-8b4c66d0b9fb
-- title:
--   Theorem 5.5 — multiclass $\ell_1$ hardcore
-- statement:
--   For all finite $\mathcal X$ and $\mathcal Y=[k]$, distributions over $(x,y)\in\mathcal X\times\mathcal Y$, finite $\mathcal C\subseteq\{\mathcal X\to\mathbb R^k\}$ and $\varepsilon>0$,
--
--   $$
--   \min_{\lambda\in\mathbb R^{\mathcal C}}\ \mathbb E\big[\|y-c_\lambda(x)\|_1\big]+\varepsilon\|\lambda\|_1\ =\ \max_{\sigma:\mathcal X\times\mathcal Y\to[-1,1]^k}\mathbb E\big[\langle y,\sigma(x,y)\rangle\big]\quad\text{s.t. }\forall c\in\mathcal C,\ \Big|\mathbb E\big[\langle c(x),\sigma(x,y)\rangle\big]\Big|\le\varepsilon,
--   $$
--
--   with both optima attained; labels are one-hot vectors.
--
--   The hardness certificate for multiclass $\ell_1$ loss is neither a measure nor a channel but a bounded signed vector field $\sigma$ whose correlation with the labels is large while every test in $\mathcal C$ sees it as nearly mean zero.
--
--   Differences from the source:
--   - encoding: labels y ∈ Y = [k] as one-hot vectors e_y → y : Fin k, with e_y = Pi.single y 1 (or [j = y] entrywise); reason: the identification of p.4
--   - encoding: a distribution over (x, y) ∈ X × Y → weights D x y with IsDist D (nonnegative, summing to 1), expectations as weighted finite sums; reason: the same distributions; zero-probability pairs allowed
--   - encoding: a finite class C ⊆ {X → ℝᵏ} and c_λ = ∑_{c∈C} λ_c c → a finite indexed family c : ι → X → ℝᵏ with c_λ = combo c λ; reason: an indexed family with ι = C recovers the set; repeated members change neither side, since splitting a coefficient among copies never lowers ε‖λ‖₁ and the constraints repeat
--   - encoding: min_λ … = max … (both sides attained) → ∃ v : ℝ, IsLeast of the range of the left objective and IsGreatest of the set of feasible right values; reason: "min" and "max" assert attainment; one common value v says the two optima are equal
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 5.5, p.27 (PDF p.29); proof p.28 (PDF p.30)

import Mathlib
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_combo

namespace MaskingHardness.Supplement

/-- **Theorem 5.5** (Multiclass ℓ1 Hardcore) (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Theorem 5.5, printed p.27 = PDF p.29; proof
printed p.28 = PDF p.30).

For all finite `X` and `Y = [k]`, distributions over `(x, y) ∈ X × Y`, finite `C ⊆ {X → ℝᵏ}` and
`ε > 0`,
`min_λ E[‖y − c_λ(x)‖₁] + ε‖λ‖₁ = max_{σ : X×Y→[−1,+1]ᵏ} E[⟨y, σ(x, y)⟩]` s.t.
`∀ c ∈ C, |E[⟨c(x), σ(x, y)⟩]| ≤ ε`.

**Formalization Note** `y` is the one-hot vector `Pi.single y 1`, so `⟨y, σ(x,y)⟩ = σ(x,y)_y`;
`‖v‖₁ = ∑_j |v_j|`; no centering is applied to `c_λ(x)`. "min = max" is one real `v` that is
`IsLeast`/`IsGreatest` on the two sides. -/
theorem theorem_5_5 {X ι : Type*} [Fintype X] [Fintype ι] {k : ℕ}
    (D : X → Fin k → ℝ) (hD : IsDist D) (c : ι → X → Fin k → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : ℝ,
      IsLeast (Set.range fun lam : ι → ℝ =>
          ∑ x, ∑ y, D x y * ∑ j, |(Pi.single y (1 : ℝ) : Fin k → ℝ) j - combo c lam x j| +
            ε * ∑ i, |lam i|) v ∧
      IsGreatest {u : ℝ | ∃ σ : X → Fin k → Fin k → ℝ,
          (∀ x y j, σ x y j ∈ Set.Icc (-1 : ℝ) 1) ∧
          (∀ i, |∑ x, ∑ y, D x y * (c i x ⬝ᵥ σ x y)| ≤ ε) ∧
          u = ∑ x, ∑ y, D x y * σ x y y} v := by sorry

end MaskingHardness.Supplement
