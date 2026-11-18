-- Prove2me | Theorems.Thm_NearLogSetCover966_Main_separator_composition_correct
-- name    : NearLogSetCover966.Main.separator_composition_correct
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T23:59:52.598429+00:00
-- url     : https://prove2.me/theorems/f7e50db8-f447-424e-ad23-8776513196de
-- title:
--   Composition preserves linear separation
-- statement:
--   Let $H_1$ consist of binary linear maps from $\mathbb F_2^D$ to $\mathbb F_2^{d_1}$, and let $H_2$ consist of such maps from $\mathbb F_2^{d_1}$ to $\mathbb F_2^{d_2}$. Suppose both families avoid zero simultaneously on every set of nonzero vectors of cardinality at most the real capacity $A$. Then
--
--   $$H_2\circ H_1\text{ has the same avoidance property},\qquad |H_2\circ H_1|\le |H_1||H_2|.$$
--
--   The composition is stored as a duplicate-free list of matrix products. This is the mathematical assertion in Lemma A.3, separated from its deterministic resource bound. No positivity assumption on $A$ is needed for this implication.
-- source:
--   Bingkai Lin and Xin Zheng, Near-Logarithmic Inapproximability of Parameterized Set Cover, STOC 2027 submission #966, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/966.pdf, Appendix A, Lemma A.3 and its proof, printed p.30 (PDF p.32).

import Definitions.Def_NearLogSetCover966_SeparatorComposition
set_option autoImplicit false

namespace NearLogSetCover966.Main

theorem separator_composition_correct {D d₁ d₂ : ℕ} (A : ℝ)
    (H₁ : HashFamily D d₁) (H₂ : HashFamily d₁ d₂)
    (h₁ : H₁.avoids A) (h₂ : H₂.avoids A) :
    (H₁.compose H₂).avoids A ∧
      (H₁.compose H₂).maps.length ≤ H₁.maps.length * H₂.maps.length := by sorry

end NearLogSetCover966.Main
