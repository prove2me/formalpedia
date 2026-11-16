-- Prove2me | Theorems.Thm_MaskingHardness_Supplement_theorem_6_4
-- name    : MaskingHardness.Supplement.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:37:41.948181+00:00
-- url     : https://prove2.me/theorems/c1dcc086-2c54-493f-93bb-b3a3cd5ebf70
-- title:
--   Theorem 6.4 — universal masking channels: properties
-- statement:
--   Fix finite $\mathcal X$ and $\mathcal Y=[k]$, a distribution over $(x,y)\in\mathcal X\times\mathcal Y$, a finite $\mathcal C\subseteq\{\mathcal X\to\mathbb R^k\}$, a model $p:\mathcal X\to\Delta_k$, and convex–concave conjugates $g:\mathcal Y\times\mathbb R^k\to\mathbb R$ and $h:\mathcal Y\times\Delta_k\to\overline{\mathbb R}$. Let $\hat c_g$ be an $\varepsilon_1$-optimal lowest-loss response and $\widehat W_h$ an $\varepsilon_2$-optimal highest-fidelity response. Then:
--
--   1. **(Hardness $\ge$ Fidelity)** if $p$ is $\widehat W_h$-weighted $(\mathcal C,\varepsilon_3)$-multiaccurate, then the masking channel $W_p=\widehat W_h\circ p$ certifies hardness: for all $c\in\mathcal C$,
--   $$
--   \mathbb E\big[g(y,\pi(c(x)))\big]\ \ge\ \mathbb E\big[h(y,W_p(x)y)\big]-\varepsilon_3 ;
--   $$
--   2. **(Hardness $\le$ Fidelity)** if $p$ is $\varepsilon_4$-duality gap calibrated, then the action $c_p=\hat c_g\circ p$ achieves
--   $$
--   \mathbb E\big[g(y,c_p(x))\big]\ \le\ \mathbb E\big[h(y,W_p(x)y)\big]+(\varepsilon_1+\varepsilon_2+\varepsilon_4).
--   $$
--
--   A single model $p$ with these two indistinguishability properties thus yields, by post-processing, a near-optimal masking channel for $h$ and a near-optimal action for $g$.
--
--   **Formalization Note** Both inequalities are in `EReal`; the responses are functions on $\mathbb R^k$ constrained at every $z\in\Delta_k$; no sign conditions on $\varepsilon_1,\dots,\varepsilon_4$ and no boundedness of the duality gap are assumed, as in the source.
--
--   Differences from the source:
--   - encoding: labels y ∈ Y = [k] as one-hot vectors e_y → y : Fin k, with e_y = Pi.single y 1 (or [j = y] entrywise); reason: the identification of p.4
--   - encoding: a distribution over (x, y) ∈ X × Y → weights D x y with IsDist D (nonnegative, summing to 1), expectations as weighted finite sums; reason: the same distributions; zero-probability pairs allowed
--   - encoding: h : Y × Δ_k → ℝ̄ (ℝ̄-valued, defined on Δ_k) → h : Fin k → (Fin k → ℝ) → EReal with h y z = ⊥ for z ∉ Δ_k (hdom); reason: Definition 2.2 judges a function given on a subset by its extension by −∞; ℝ̄ is EReal
--   - encoding: convex–concave conjugates g : Y × ℝᵏ → ℝ, h : Y × Δ_k → ℝ̄ (Definitions 2.6, 2.7) → ∀ y, IsConvConcConj (fun a => (g y a : EReal)) (h y), the published base predicate; reason: Definition 2.7 is Definition 2.6 for each y; the base predicate writes out the two formulas and properness, which imply closedness and (con)vexity
--   - encoding: responses ĉ_g : Δ_k → ℝᵏ and Ŵ_h : Δ_k → Δ_k^k → functions on ℝᵏ whose defining conditions (IsLowestLossResponse, IsHighestFidelityResponse) are imposed at every z ∈ Δ_k; reason: values off Δ_k are never used, and every response on Δ_k extends to ℝᵏ
--   - encoding: "within γ of the infimum / maximum" → E[g(y, ĉ_g(z))] ≤ inf + γ and sup ≤ E[h(y, Ŵ_h(z)y)] + γ, in EReal; reason: the same conditions with the optima possibly infinite
--   - encoding: Gap(z) ∈ ℝ̄ᵏ and E[⟨Gap(p(x)), y − p(x)⟩], the expectations in (a) and (b) → EReal sums with 0·(±∞) = 0 and (+∞) + (−∞) = −∞; the conclusions compare EReal values; reason: ℝ̄ is EReal; with finite values these are the real expressions
--   - encoding: a finite class C ⊆ {X → ℝᵏ}, 'for all c ∈ C' → a finite indexed family c : ι → X → ℝᵏ with [Fintype ι], 'for all i'; reason: an indexed family with ι = C recovers the set; repeated members repeat the same hypothesis and conclusion
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 6.4, p.30 (PDF p.32); proof p.31 (PDF p.33)

import Mathlib
import Definitions.Def_MaskingHardness_IsConvConcConj
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_centered
import Definitions.Def_MaskingHardness_channelFidelity
import Definitions.Def_MaskingHardness_Supplement_IsLowestLossResponse
import Definitions.Def_MaskingHardness_Supplement_IsHighestFidelityResponse
import Definitions.Def_MaskingHardness_Supplement_IsChannelWeightedMultiaccurate
import Definitions.Def_MaskingHardness_Supplement_IsDualityGapCalibrated

namespace MaskingHardness.Supplement

/-- **Theorem 6.4** (Universal Masking Channels – Properties) (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Theorem 6.4, printed p.30 =
PDF p.32; proof printed p.31 = PDF p.33).

Fix finite `X` and `Y = [k]`, a distribution over `(x, y) ∈ X × Y`, finite `C ⊆ {X → ℝᵏ}`, a model
`p : X → Δ_k`, and convex–concave conjugates `g : Y × ℝᵏ → ℝ`, `h : Y × Δ_k → ℝ̄`. Let `ĉ_g` be an
`ε1`-optimal lowest-loss response and `Ŵ_h` an `ε2`-optimal highest-fidelity response. Then
(a) if `p` is `Ŵ_h`-weighted `(C, ε3)`-multiaccurate, then for all `c ∈ C`,
`E[g(y, π(c(x)))] ≥ E[h(y, W_p(x)y)] − ε3` with `W_p = Ŵ_h ∘ p`;
(b) if `p` is `ε4`-duality gap calibrated, then
`E[g(y, c_p(x))] ≤ E[h(y, W_p(x)y)] + (ε1 + ε2 + ε4)` with `c_p = ĉ_g ∘ p`.

**Formalization Note** ℝ̄ is `EReal`; `h` is `−∞` off `Δ_k` (`hdom`); the conjugacy is
`∀ y, IsConvConcConj (g y) (h y)`. Both inequalities are in `EReal`, with `E[h(y, W_p(x)y)]` the
published `channelFidelity`. The responses are functions on `ℝᵏ` constrained at every `z ∈ Δ_k`.
No sign conditions on `ε1, …, ε4` and no boundedness of `Gap` are assumed (the paper states none). -/
theorem theorem_6_4 {X ι : Type*} [Fintype X] [Fintype ι] {k : ℕ}
    (D : X → Fin k → ℝ) (hD : IsDist D) (c : ι → X → Fin k → ℝ)
    (p : X → Fin k → ℝ) (hp : ∀ x, p x ∈ stdSimplex ℝ (Fin k))
    (g : Fin k → (Fin k → ℝ) → ℝ) (h : Fin k → (Fin k → ℝ) → EReal)
    (hdom : ∀ y z, z ∉ stdSimplex ℝ (Fin k) → h y z = ⊥)
    (hgh : ∀ y, IsConvConcConj (fun a => ((g y a : ℝ) : EReal)) (h y))
    (ε₁ ε₂ ε₃ ε₄ : ℝ)
    (chat : (Fin k → ℝ) → (Fin k → ℝ)) (hchat : IsLowestLossResponse g ε₁ chat)
    (What : (Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ) (hWhat : IsHighestFidelityResponse h ε₂ What) :
    (IsChannelWeightedMultiaccurate D c What ε₃ p →
      ∀ i, channelFidelity D h (fun x => What (p x)) - (ε₃ : EReal) ≤
        (((∑ x, ∑ y, D x y * g y (centered (c i x)) : ℝ)) : EReal)) ∧
    (IsDualityGapCalibrated D g h chat What ε₄ p →
      (((∑ x, ∑ y, D x y * g y (chat (p x)) : ℝ)) : EReal) ≤
        channelFidelity D h (fun x => What (p x)) + ((ε₁ + ε₂ + ε₄ : ℝ) : EReal)) := by sorry

end MaskingHardness.Supplement
