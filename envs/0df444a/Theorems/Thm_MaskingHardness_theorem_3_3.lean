-- Prove2me | Theorems.Thm_MaskingHardness_theorem_3_3
-- name    : MaskingHardness.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:50:21.828359+00:00
-- url     : https://prove2.me/theorems/1b279bb0-4f2f-43b1-9937-3dc56fc1b8a4
-- title:
--   Theorem 3.3 — six functions: $\inf_a\mathbb E[g(y,a)]+R(a)=\sup_b\mathbb E[h(y,b)]+S(-b)$, with attainment if finite
-- statement:
--   Fix finite sets $\mathcal X,\mathcal Y$, a distribution $\mathcal D$ over $(x,y)\in\mathcal X\times\mathcal Y$, functions $g,h:\mathcal Y\times\mathbb R^k\to\overline{\mathbb R}$ and functionals $R,S:(\mathcal X\times\mathcal Y\to\mathbb R^k)\to\overline{\mathbb R}$. Assume:
--
--   1. (a) $g$ and $h$ are two-input convex–concave conjugates (Definition 2.7);
--   2. (b) $R$ and $S$ are convex–concave conjugates (Definition 2.6) under $\langle a,b\rangle_{\mathcal D}=\mathbb E_{\mathcal D}[\langle a(x,y),b(x,y)\rangle]$;
--   3. (c) at least one of $g,h,R,S$ is finite everywhere;
--   4. (footnote 17) $R(a)$ and $S(b)$ depend only on the values of $a$, $b$ at pairs $(x,y)$ of positive probability: if $a_1=a_2$ $\mathcal D$-almost surely then $R(a_1)=R(a_2)$, and likewise for $S$.
--
--   Then strong duality holds:
--
--   $$
--   \inf_{a:\mathcal X\times\mathcal Y\to\mathbb R^k}\mathbb E[g(y,a(x,y))]+R(a)=\sup_{b:\mathcal X\times\mathcal Y\to\mathbb R^k}\mathbb E[h(y,b(x,y))]+S(-b). \tag{9}
--   $$
--
--   Moreover, if the finite function is $g$ or $R$, the supremum in (9) is attained whenever it is finite; if the finite function is $h$ or $S$, the infimum in (9) is attained whenever it is finite.
--
--   This general framework, applied with different pairs $(R,S)$, yields the paper's main theorem and its variants.
--
--   **Formalization Note** Expectations of extended-real terms are $\mathcal D$-weighted sums in `EReal` with $0\cdot(\pm\infty)=0$; functions on $\mathcal X\times\mathcal Y$ are curried; "finite" is "$\neq\pm\infty$".
--
--   Differences from the source:
--   - encoding: a distribution D over X × Y → weights D x y ≥ 0 summing to 1 (IsDist); expectations are the weighted finite sums; reason: finite sets; same distributions, zero-probability pairs allowed
--   - encoding: E[v(x, y)] for an ℝ̄-valued v → ∑ₓ ∑_y D x y · v x y in EReal, with 0 · (±∞) = 0; reason: pairs of probability zero do not contribute, as in the paper's treatment of D-null pairs (footnotes 17, 18)
--   - encoding: (b) R, S convex–concave conjugates as in Definition 2.6 under ⟨a, b⟩_D → IsConvConcConjWith (pairD D) R S: the two conjugacy formulas for the pairing ⟨·,·⟩_D plus properness; reason: closedness and (con)vexity follow from the formulas; equivalent predicates
--   - encoding: footnote 17: R(a) and S(−b) depend only on values at positive-probability pairs → hypotheses hR, hS: D-a.s. equal arguments give equal values of R and of S; reason: b ↦ −b preserves D-a.s. equality, so the condition on S(−b) and on S(b) coincide
--   - encoding: attained if finite → the value ≠ ⊤ and ≠ ⊥ implies an argument attaining it; reason: definition of attainment; 'finite' means real-valued
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 3.3, Eq. (9), with footnote 17, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_MaskingHardness_IsConvConcConjWith
import Definitions.Def_MaskingHardness_IsConvConcConj
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_pairD

namespace MaskingHardness

/-- **Theorem 3.3** (Six Functions) (Gopalan–Prabhakaran–Tankala, *Universal Hardness From
Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Theorem 3.3, Eq. (9) and
footnote 17, printed p.21 = PDF p.23).

Fix finite sets `X, Y`, a distribution `D` over `(x, y) ∈ X × Y`, functions
`g, h : Y × ℝᵏ → ℝ̄` and functionals `R, S : (X × Y → ℝᵏ) → ℝ̄`. Assume
(a) `g, h` are two-input convex–concave conjugates (Definition 2.7);
(b) `R, S` are convex–concave conjugates (Definition 2.6) under `⟨a, b⟩_D = E_D[⟨a(x,y), b(x,y)⟩]`;
(c) at least one of `g, h, R, S` is finite everywhere;
and (footnote 17) `R(a)` and `S(b)` depend only on the values at pairs of positive probability.
Then
`inf_a E[g(y, a(x, y))] + R(a) = sup_b E[h(y, b(x, y))] + S(−b)`.
If the finite function is one of `g, R`, the supremum is attained if finite; if it is one of
`h, S`, the infimum is attained if finite.

**Formalization Note** ℝ̄ is `EReal`; expectations of ℝ̄-valued terms are `∑ₓ ∑_y D(x,y) · v` in
`EReal` (`0 · (±∞) = 0`); functions on `X × Y` are curried. -/
theorem theorem_3_3 {X Y : Type*} [Fintype X] [Fintype Y] {k : ℕ}
    (D : X → Y → ℝ) (hD : IsDist D)
    (g h : Y → (Fin k → ℝ) → EReal) (R S : (X → Y → Fin k → ℝ) → EReal)
    (ha : ∀ y, IsConvConcConj (g y) (h y))
    (hb : IsConvConcConjWith (pairD D) R S)
    (hc : (∀ y t, g y t ≠ ⊤ ∧ g y t ≠ ⊥) ∨ (∀ y t, h y t ≠ ⊤ ∧ h y t ≠ ⊥) ∨
      (∀ a, R a ≠ ⊤ ∧ R a ≠ ⊥) ∨ (∀ b, S b ≠ ⊤ ∧ S b ≠ ⊥))
    (hR : ∀ a₁ a₂ : X → Y → Fin k → ℝ, (∀ x y, 0 < D x y → a₁ x y = a₂ x y) → R a₁ = R a₂)
    (hS : ∀ b₁ b₂ : X → Y → Fin k → ℝ, (∀ x y, 0 < D x y → b₁ x y = b₂ x y) → S b₁ = S b₂) :
    ((⨅ a : X → Y → Fin k → ℝ, (∑ x, ∑ y, ((D x y : ℝ) : EReal) * g y (a x y)) + R a) =
      ⨆ b : X → Y → Fin k → ℝ, (∑ x, ∑ y, ((D x y : ℝ) : EReal) * h y (b x y)) + S (-b)) ∧
    ((∀ y t, g y t ≠ ⊤ ∧ g y t ≠ ⊥) ∨ (∀ a, R a ≠ ⊤ ∧ R a ≠ ⊥) →
      (⨆ b : X → Y → Fin k → ℝ, (∑ x, ∑ y, ((D x y : ℝ) : EReal) * h y (b x y)) + S (-b)) ≠ ⊤ →
      (⨆ b : X → Y → Fin k → ℝ, (∑ x, ∑ y, ((D x y : ℝ) : EReal) * h y (b x y)) + S (-b)) ≠ ⊥ →
      ∃ bstar : X → Y → Fin k → ℝ,
        (∑ x, ∑ y, ((D x y : ℝ) : EReal) * h y (bstar x y)) + S (-bstar) =
          ⨆ b : X → Y → Fin k → ℝ, (∑ x, ∑ y, ((D x y : ℝ) : EReal) * h y (b x y)) + S (-b)) ∧
    ((∀ y t, h y t ≠ ⊤ ∧ h y t ≠ ⊥) ∨ (∀ b, S b ≠ ⊤ ∧ S b ≠ ⊥) →
      (⨅ a : X → Y → Fin k → ℝ, (∑ x, ∑ y, ((D x y : ℝ) : EReal) * g y (a x y)) + R a) ≠ ⊤ →
      (⨅ a : X → Y → Fin k → ℝ, (∑ x, ∑ y, ((D x y : ℝ) : EReal) * g y (a x y)) + R a) ≠ ⊥ →
      ∃ astar : X → Y → Fin k → ℝ,
        (∑ x, ∑ y, ((D x y : ℝ) : EReal) * g y (astar x y)) + R astar =
          ⨅ a : X → Y → Fin k → ℝ, (∑ x, ∑ y, ((D x y : ℝ) : EReal) * g y (a x y)) + R a) := by sorry

end MaskingHardness
