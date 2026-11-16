-- Prove2me | Theorems.Thm_MaskingHardness_Supplement_theorem_4_1
-- name    : MaskingHardness.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:36:30.175641+00:00
-- url     : https://prove2.me/theorems/15b9dc2a-1793-4acf-bf53-45b80e0ad398
-- title:
--   Theorem 4.1 — hardness vs fidelity, soft penalty
-- statement:
--   For all finite $\mathcal X$ and $\mathcal Y=[k]$, distributions over $(x,y)\in\mathcal X\times\mathcal Y$, compact convex $\mathcal C\subseteq\{\mathcal X\to\mathbb R^k\}$, and convex–concave conjugates $g:\mathcal Y\times\mathbb R^k\to\mathbb R$ and $h:\mathcal Y\times\Delta_k\to\overline{\mathbb R}$,
--
--   $$
--   \min_{c\in\mathcal C}\ \mathbb E\big[g(y,\pi(c(x)))\big]\ =\ \max_{W:\mathcal X\to\Delta_k^k}\Big(\mathbb E\big[h(y,W(x)y)\big]-\max_{c\in\mathcal C}\mathbb E\big[\langle c(x),\,W(x)y-\vec1/k\rangle\big]\Big).
--   $$
--
--   Compared with Theorem 1.9 the hardcore constraint is replaced by a soft penalty, the largest advantage of a test in $\mathcal C$ against the channel, and the class is any compact convex set of functions rather than the $\ell_1$-regularized span of a finite class.
--
--   **Formalization Note** $\mathcal C$ is a nonempty compact convex subset of $\mathcal X\to\mathbb R^k$; "min = max" is one real $v$ that is `IsLeast` of the left values and `IsGreatest` of the right values; the inner maximum is a real $m$ given by `IsGreatest`, and $\mathbb E[h(y,W(x)y)]-m$ is computed in `EReal`.
--
--   Differences from the source:
--   - encoding: labels y ∈ Y = [k] as one-hot vectors e_y → y : Fin k, with e_y = Pi.single y 1 (or [j = y] entrywise); reason: the identification of p.4
--   - encoding: a distribution over (x, y) ∈ X × Y → weights D x y with IsDist D (nonnegative, summing to 1), expectations as weighted finite sums; reason: the same distributions; zero-probability pairs allowed
--   - encoding: h : Y × Δ_k → ℝ̄ (ℝ̄-valued, defined on Δ_k) → h : Fin k → (Fin k → ℝ) → EReal with h y z = ⊥ for z ∉ Δ_k (hdom); reason: Definition 2.2 judges a function given on a subset by its extension by −∞; ℝ̄ is EReal
--   - encoding: convex–concave conjugates g : Y × ℝᵏ → ℝ, h : Y × Δ_k → ℝ̄ (Definitions 2.6, 2.7) → ∀ y, IsConvConcConj (fun a => (g y a : EReal)) (h y), the published base predicate; reason: Definition 2.7 is Definition 2.6 for each y; the base predicate writes out the two formulas and properness, which imply closedness and (con)vexity
--   - reading: compact convex C ⊆ {X → ℝᵏ} with min_{c∈C} → C : Set (X → Fin k → ℝ) compact, convex and nonempty; reason: a minimum over C presupposes C ≠ ∅; for C = ∅ the left side does not exist
--   - encoding: min_{c∈C} … = max_W (E[h(y, W(x)y)] − max_{c∈C} E[⟨c(x), W(x)y − 1⃗/k⟩]) → ∃ v : ℝ, IsLeast of the left values over C, and IsGreatest of {channelFidelity D h W − m : W noisy, m the IsGreatest inner value} at v, in EReal; reason: max and min assert attainment; the inner maximum of a continuous linear function on a nonempty compact set always exists, and fidelities may be −∞
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 4.1, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_MaskingHardness_IsConvConcConj
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_centered
import Definitions.Def_MaskingHardness_IsNoisyChannel
import Definitions.Def_MaskingHardness_channelFidelity

namespace MaskingHardness.Supplement

/-- **Theorem 4.1** (Hardness vs Fidelity, Soft Penalty) (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Theorem 4.1, printed p.23 = PDF
p.25).

For all finite `X` and `Y = [k]`, distributions over `(x, y) ∈ X × Y`, compact convex
`C ⊆ {X → ℝᵏ}`, and convex–concave conjugates `g : Y × ℝᵏ → ℝ`, `h : Y × Δ_k → ℝ̄`,
`min_{c ∈ C} E[g(y, π(c(x)))] = max_{W : X → Δ_k^k} (E[h(y, W(x)y)] − max_{c ∈ C} E[⟨c(x), W(x)y − 1⃗/k⟩])`.

**Formalization Note** `C` is a set in the finite-dimensional space `X → ℝᵏ` (product topology),
compact, convex and nonempty (the minimum over `C` presupposes `C ≠ ∅`). "min = max" is one real
`v` that is `IsLeast` of the left values over `C` and `IsGreatest` of the right values over all
noisy channels `W`; the inner maximum over `C` is a real `m` with `IsGreatest`, and the outer
objective `E[h(y, W(x)y)] − m` is computed in `EReal` (`channelFidelity`). `h` is `−∞` off `Δ_k`
(`hdom`); the conjugacy is `∀ y, IsConvConcConj (g y) (h y)` (Definitions 2.6, 2.7). -/
theorem theorem_4_1 {X : Type*} [Fintype X] {k : ℕ}
    (D : X → Fin k → ℝ) (hD : IsDist D) (C : Set (X → Fin k → ℝ))
    (hCc : IsCompact C) (hCv : Convex ℝ C) (hCn : C.Nonempty)
    (g : Fin k → (Fin k → ℝ) → ℝ) (h : Fin k → (Fin k → ℝ) → EReal)
    (hdom : ∀ y z, z ∉ stdSimplex ℝ (Fin k) → h y z = ⊥)
    (hgh : ∀ y, IsConvConcConj (fun a => ((g y a : ℝ) : EReal)) (h y)) :
    ∃ v : ℝ,
      IsLeast ((fun c : X → Fin k → ℝ => ∑ x, ∑ y, D x y * g y (centered (c x))) '' C) v ∧
      IsGreatest {u : EReal | ∃ W : X → Matrix (Fin k) (Fin k) ℝ, IsNoisyChannel W ∧
          ∃ m : ℝ, IsGreatest ((fun c : X → Fin k → ℝ => ∑ x, ∑ y,
              D x y * (c x ⬝ᵥ (fun j => W x j y - (k : ℝ)⁻¹))) '' C) m ∧
            u = channelFidelity D h W - (m : EReal)} (v : EReal) := by sorry

end MaskingHardness.Supplement
