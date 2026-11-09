-- Prove2me | Theorems.Thm_MaskingHardness_theorem_2_9
-- name    : MaskingHardness.theorem_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:49:48.151511+00:00
-- url     : https://prove2.me/theorems/14fce7ca-effe-4834-9321-9b2e5fba7ac6
-- title:
--   Theorem 2.9 — Fenchel duality (special case): $\inf_a g_1+g_2=\sup_b h_1(b)+h_2(-b)$, with attainment
-- statement:
--   Let $g_1,h_1:\mathbb R^n\to\overline{\mathbb R}$ and $g_2,h_2:\mathbb R^n\to\overline{\mathbb R}$ be two pairs of convex–concave conjugates (Definition 2.6). Suppose at least one of the four functions is finite everywhere (never takes the value $\pm\infty$). Then
--
--   $$
--   \inf_{a\in\mathbb R^n} g_1(a)+g_2(a)=\sup_{b\in\mathbb R^n} h_1(b)+h_2(-b). \tag{6}
--   $$
--
--   Moreover:
--
--   1. if the finite function is $g_1$ or $g_2$, the supremum on the right is attained at some $b^\star\in\mathbb R^n$;
--   2. if the finite function is $h_1$ or $h_2$, the infimum on the left is attained at some $a^\star\in\mathbb R^n$.
--
--   This is the special case of Fenchel's duality theorem [Rockafellar 1970] on which the paper's general six-functions theorem rests.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ` with the dot product, $\overline{\mathbb R}$ is `EReal`, "finite everywhere" is `∀ a, f a ≠ ⊤ ∧ f a ≠ ⊥`, and attainment is equality of the value at the point with the infimum/supremum. Properness keeps both sides free of the undefined sum $(+\infty)+(-\infty)$.
--
--   Differences from the source:
--   - encoding: ℝⁿ with the standard inner product; ℝ̄ → Fin n → ℝ with dotProduct; EReal; reason: Lean convention; same spaces
--   - encoding: convex–concave conjugates (Definition 2.6: closed proper convex g, closed proper concave h, conjugacy formulas) → IsConvConcConj: the two conjugacy formulas plus properness of g and h; reason: closedness and (con)vexity follow from the formulas (suprema/infima of affine functions); equivalent predicates
--   - encoding: the supremum is achieved by some particular b∗ (resp. the infimum by some a∗) → ∃ b⋆ with h₁ b⋆ + h₂ (−b⋆) equal to the supremum (resp. ∃ a⋆ with g₁ a⋆ + g₂ a⋆ equal to the infimum); reason: definition of attainment
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 2.9, Eq. (6), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_MaskingHardness_IsConvConcConj

namespace MaskingHardness

/-- **Theorem 2.9** (Fenchel's Duality Theorem, Special Case [Roc70]) (Gopalan–Prabhakaran–Tankala,
*Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d,
Theorem 2.9, Eq. (6), printed p.17 = PDF p.19).

Let `g₁, h₁ : ℝⁿ → ℝ̄` and `g₂, h₂ : ℝⁿ → ℝ̄` be two convex–concave conjugate pairs. If at least
one of the four functions is finite everywhere, then
`inf_a g₁(a) + g₂(a) = sup_b h₁(b) + h₂(−b)`. If the finite function is one of `g₁, g₂`, the
supremum is achieved by some `b⋆`; if it is one of `h₁, h₂`, the infimum is achieved by some `a⋆`.

**Formalization Note** ℝⁿ is `Fin n → ℝ`, ℝ̄ is `EReal`; "finite everywhere" is
`∀ a, f a ≠ ⊤ ∧ f a ≠ ⊥`. Properness makes both sums free of `⊥ + ⊤`. -/
theorem theorem_2_9 {n : ℕ} (g₁ h₁ g₂ h₂ : (Fin n → ℝ) → EReal)
    (hp₁ : IsConvConcConj g₁ h₁) (hp₂ : IsConvConcConj g₂ h₂)
    (hfin : (∀ a, g₁ a ≠ ⊤ ∧ g₁ a ≠ ⊥) ∨ (∀ a, g₂ a ≠ ⊤ ∧ g₂ a ≠ ⊥) ∨
      (∀ b, h₁ b ≠ ⊤ ∧ h₁ b ≠ ⊥) ∨ (∀ b, h₂ b ≠ ⊤ ∧ h₂ b ≠ ⊥)) :
    (⨅ a, g₁ a + g₂ a) = (⨆ b, h₁ b + h₂ (-b)) ∧
    ((∀ a, g₁ a ≠ ⊤ ∧ g₁ a ≠ ⊥) ∨ (∀ a, g₂ a ≠ ⊤ ∧ g₂ a ≠ ⊥) →
      ∃ bstar, h₁ bstar + h₂ (-bstar) = ⨆ b, h₁ b + h₂ (-b)) ∧
    ((∀ b, h₁ b ≠ ⊤ ∧ h₁ b ≠ ⊥) ∨ (∀ b, h₂ b ≠ ⊤ ∧ h₂ b ≠ ⊥) →
      ∃ astar, g₁ astar + g₂ astar = ⨅ a, g₁ a + g₂ a) := by sorry

end MaskingHardness
