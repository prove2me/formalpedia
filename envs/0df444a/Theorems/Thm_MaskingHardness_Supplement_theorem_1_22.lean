-- Prove2me | Theorems.Thm_MaskingHardness_Supplement_theorem_1_22
-- name    : MaskingHardness.Supplement.theorem_1_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:35:49.78521+00:00
-- url     : https://prove2.me/theorems/601f6005-819f-424c-8018-481c0c483d7a
-- title:
--   Theorem 1.22 — characterizing pseudoentropy using MaxEnt
-- statement:
--   For all finite $\mathcal X$ and $\mathcal Y=[k]$, distributions $\mathcal D$ over pairs $(x,y)\in\mathcal X\times\mathcal Y$, finite $\mathcal C\subseteq\{\mathcal X\to\mathbb R^k\}$ and convex–concave conjugate pairs $g:\mathbb R^k\to\mathbb R$ and $h:\Delta_k\to\overline{\mathbb R}$, let $\ell(y,\eta)=g(-\eta)-\langle y,\eta\rangle$ be the associated GLM loss. Then for all $\varepsilon\ge0$:
--
--   1. the regularized GLM loss equals the maximum entropy of an indistinguishable model, the maximum being attained:
--   $$
--   \inf_{\lambda\in\mathbb R^{\mathcal C}}\ \mathbb E\big[\ell(y,c_\lambda(x))\big]+\varepsilon\|\lambda\|_1\ =\ \max_{p:\mathcal X\to\Delta_k}\mathbb E\big[h(p(x))\big]\quad\text{s.t. }p(x)\text{ is }(\mathcal C,\varepsilon)\text{-indistinguishable from }y;
--   $$
--   2. (footnote 20) when $\varepsilon\neq0$ and $\ell$ is bounded below, the infimum on the left is a minimum.
--
--   Here "$(\mathcal C,\varepsilon)$-indistinguishable" is $(\mathcal C,\varepsilon)$-multiaccuracy: $|\mathbb E[\langle c(x),y-p(x)\rangle]|\le\varepsilon$ for all $c\in\mathcal C$. The model $p$ depends on $x$ only. The theorem identifies pseudoentropy (the largest $h$-entropy of a model indistinguishable from the labels) with the hardness of $\ell_1$-regularized GLM loss minimization over $\mathrm{span}(\mathcal C)$, the dual of the MaxEnt program.
--
--   **Formalization Note** The infimum is taken in `EReal`; "max" is `IsGreatest`, "minimum" is `IsLeast` of the range; $\mathbb E[h(p(x))]=\sum_{x,y}\mathcal D(x,y)h(p(x))$ in `EReal`.
--
--   Differences from the source:
--   - encoding: labels y ∈ Y = [k] as one-hot vectors e_y → y : Fin k, with e_y = Pi.single y 1 (or [j = y] entrywise); reason: the identification of p.4
--   - encoding: a distribution over (x, y) ∈ X × Y → weights D x y with IsDist D (nonnegative, summing to 1), expectations as weighted finite sums; reason: the same distributions; zero-probability pairs allowed
--   - encoding: a finite class C ⊆ {X → ℝᵏ} and c_λ = ∑_{c∈C} λ_c c → a finite indexed family c : ι → X → ℝᵏ with c_λ = combo c λ; reason: an indexed family with ι = C recovers the set; repeated members change neither side, since splitting a coefficient among copies never lowers ε‖λ‖₁ and the constraints repeat
--   - encoding: h : Δ_k → ℝ̄ and g, h convex–concave conjugates (Definition 2.6) → h : (Fin k → ℝ) → EReal with h z = ⊥ off Δ_k (hdom) and IsConvConcConj (fun a => (g a : EReal)) h; reason: Definition 2.2 extends h by −∞ off Δ_k; the base predicate is Definition 2.6
--   - reading: p(x) is (C, ε)-indistinguishable from y → IsMultiaccurate D c ε p (Definition 2.16) with p x ∈ Δ_k; reason: the proof on p.36 reads the constraint as "(C, ε)-multiaccurate (i.e. feasible for the maximization problem)"
--   - encoding: inf … = max …; "the infimum can be replaced with a minimum" → IsGreatest of the feasible EReal values at the EReal infimum; ∃ λ₀, IsLeast of the range at λ₀; reason: the infimum may be −∞ a priori, so it is taken in EReal; max and min assert attainment
--   - encoding: ε ≠ 0 and ℓ bounded below → 0 < ε and ∃ v, ∀ y η, v ≤ g(−η) − η_y; reason: ε ≥ 0 is assumed, so ε ≠ 0 is ε > 0
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 1.22 with footnote 20, p.35 (PDF p.37), proof p.36 (PDF p.38); first stated pp.13–14 (PDF pp.15–16) with footnote 13

import Mathlib
import Definitions.Def_MaskingHardness_IsConvConcConj
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_combo
import Definitions.Def_MaskingHardness_Supplement_IsMultiaccurate

namespace MaskingHardness.Supplement

/-- **Theorem 1.22** (Characterizing pseudoentropy using MaxEnt) (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Theorem 1.22 with footnote
20, printed p.35 = PDF p.37, proof p.36 = PDF p.38; first stated printed pp.13–14 = PDF pp.15–16
with footnote 13).

For all finite `X` and `Y = [k]`, distributions `D` over pairs `(x, y) ∈ X × Y`, finite
`C ⊆ {X → ℝᵏ}` and convex–concave conjugate pairs `g : ℝᵏ → ℝ`, `h : Δ_k → ℝ̄`, let
`ℓ(y, η) = g(−η) − ⟨y, η⟩` (GLM loss). Then for all `ε ≥ 0`:
(i) `inf_λ E[ℓ(y, c_λ(x))] + ε‖λ‖₁ = max_{p : X → Δ_k} E[h(p(x))]` s.t. `p(x)` is
`(C, ε)`-indistinguishable from `y`, the maximum being attained;
(ii) (footnote 20) when `ε ≠ 0` and `ℓ` is bounded below, the infimum is a minimum.

**Formalization Note** ℝ̄ is `EReal`; `h` is given on `ℝᵏ` and is `−∞` off `Δ_k` (`hdom`); the
conjugacy is the published `IsConvConcConj` (Definition 2.6) of `a ↦ g(a)` and `h`. The infimum in
(i) is taken in `EReal`; "max" is `IsGreatest`, "minimum" is `IsLeast` of the range.
"`(C, ε)`-indistinguishable from `y`" is `(C, ε)`-multiaccuracy (Definition 2.16, `IsMultiaccurate`),
the reading of the proof on p.36. `⟨y, η⟩ = η_y`; `p` depends on `x` only; `E[h(p(x))]` is
`∑ₓ ∑_y D(x, y) h(p(x))` in `EReal`. -/
theorem theorem_1_22 {X ι : Type*} [Fintype X] [Fintype ι] {k : ℕ}
    (D : X → Fin k → ℝ) (hD : IsDist D) (c : ι → X → Fin k → ℝ)
    (g : (Fin k → ℝ) → ℝ) (h : (Fin k → ℝ) → EReal)
    (hdom : ∀ z, z ∉ stdSimplex ℝ (Fin k) → h z = ⊥)
    (hgh : IsConvConcConj (fun a => ((g a : ℝ) : EReal)) h)
    (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest
        {v : EReal | ∃ p : X → Fin k → ℝ, (∀ x, p x ∈ stdSimplex ℝ (Fin k)) ∧
          IsMultiaccurate D c ε p ∧ v = ∑ x, ∑ y, ((D x y : ℝ) : EReal) * h (p x)}
        (⨅ lam : ι → ℝ, (((∑ x, ∑ y, D x y * (g (-combo c lam x) - combo c lam x y) +
          ε * ∑ i, |lam i| : ℝ)) : EReal)) ∧
      (0 < ε → (∃ v : ℝ, ∀ (y : Fin k) (η : Fin k → ℝ), v ≤ g (-η) - η y) →
        ∃ lam₀ : ι → ℝ, IsLeast
          (Set.range fun lam : ι → ℝ =>
            ∑ x, ∑ y, D x y * (g (-combo c lam x) - combo c lam x y) + ε * ∑ i, |lam i|)
          (∑ x, ∑ y, D x y * (g (-combo c lam₀ x) - combo c lam₀ x y) + ε * ∑ i, |lam₀ i|)) := by sorry

end MaskingHardness.Supplement
