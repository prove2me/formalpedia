-- Prove2me | Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_lemma_2_1_construction_v2
-- name    : OAI.FiniteAlgebraicEnvelopes.lemma_2_1_construction_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-12T19:40:57.081321+00:00
-- url     : https://prove2.me/theorems/89b01df5-2d4f-46b7-b132-f61f2059d0d4
-- title:
--   Lemma 2.1, group-theoretic half (an HNN enlargement of H×H)
-- statement:
--   Let $H$ be a finitely generated group, $A = \{(h,h) : h \in H\} \le H \times H$ the diagonal subgroup, $B = \{(1,h) : h \in H\} \le H \times H$ the second-factor subgroup, and $\varphi : A \to B$ the isomorphism $(h,h) \mapsto (1,h)$ (the `Definitions.lemma_2_1_data` module). Then the HNN extension $\hat H = \mathrm{HNN}(H \times H, A, B, \varphi)$ (Mathlib's `HNNExtension (H×H) A B φ`) is finitely generated, the canonical map $H \times H \to \hat H$ is injective, and its stable letter $s$ satisfies $s(h,h)s^{-1}(h,h)^{-1} = (h,1)$ for every $h \in H$.
--
--   This is the purely group-theoretic half of the preprint's Lemma 2.1 (used in its proof of Theorem 1.2, its principal intermediate result towards the Boone–Higman conjecture). The companion fact that $\hat H$ again has decidable word problem when $H$ does is the lemma's genuinely algorithmic content, stated separately as `lemma_2_1_decidability_v2`, since it needs a dedicated computable pinch-reduction procedure rather than the general (classically-constructed, non-computable) normal form theory already in Mathlib's `HNNExtension` library.
--
--   **Formalization Note** Finite generation and injectivity of $H \times H \hookrightarrow \hat H$ follow by general HNN-extension theory (`HNNExtension.of_injective`, together with generation of the HNN extension by the image of $H$ and the stable letter, proved here since Mathlib does not yet state it). The commutator identity is Mathlib's `HNNExtension.equiv_eq_conj` specialized to $a = (h,h)^{-1} \in A$. (Resubmission of `lemma_2_1_construction`: that version's preamble incorrectly held raw `def`s instead of importing them from a `submit-definition` module, which the platform does not support and which produced an unresolvable solution-checking error.)
-- source:
--   OpenAI, *Finite algebraic envelopes and the Boone–Higman conjecture*, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf, Lemma 2.1, p. 3.

import Mathlib
import Mathlib.GroupTheory.HNNExtension
import Definitions.Def_lemma_2_1_data

namespace OAI
namespace FiniteAlgebraicEnvelopes

universe u

theorem lemma_2_1_construction_v2 {H : Type u} [Group H] [Group.FG H] :
    Group.FG (HNNExtension (H × H) (diagonalSubgroup H) (secondFactorSubgroup H)
        (diagonalEquivSecondFactor H)) ∧
    Function.Injective
      (HNNExtension.of : H × H →*
        HNNExtension (H × H) (diagonalSubgroup H) (secondFactorSubgroup H)
          (diagonalEquivSecondFactor H)) ∧
    ∀ g : H, (HNNExtension.of ((g, g) : H × H) :
          HNNExtension (H × H) (diagonalSubgroup H) (secondFactorSubgroup H)
            (diagonalEquivSecondFactor H)) *
        HNNExtension.t * (HNNExtension.of ((g, g) : H × H))⁻¹ * HNNExtension.t⁻¹
        = HNNExtension.of ((g, 1) : H × H) := by
  sorry

end FiniteAlgebraicEnvelopes
end OAI
