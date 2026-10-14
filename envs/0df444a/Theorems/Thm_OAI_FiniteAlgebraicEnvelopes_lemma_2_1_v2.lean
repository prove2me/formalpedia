-- Prove2me | Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_lemma_2_1_v2
-- name    : OAI.FiniteAlgebraicEnvelopes.lemma_2_1_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-12T19:40:48.838917+00:00
-- url     : https://prove2.me/theorems/ad86a8dd-4e8f-4dbb-ae9b-6c00392ac766
-- title:
--   Lemma 2.1 (full statement)
-- statement:
--   Lemma 2.1 of the preprint, in full: a finitely generated group $H$ with decidable word problem embeds, via $(h,h') \mapsto (h,h')$, into a group $K$ that is again finitely generated with decidable word problem, and carries an element $s$ with $s(h,h)s^{-1}(h,h)^{-1} = (h,1)$ for every $h \in H$.
--
--   This bundles `lemma_2_1_construction_v2` (the group-theoretic facts about the explicit HNN extension $\hat H = \mathrm{HNN}(H\times H, A, B, \varphi)$) with `lemma_2_1_decidability_v2` (that $\hat H$'s word problem is again decidable) into the single existential statement the preprint uses. Lemma 2.1 is used, together with Theorem 2.2, inside the preprint's proof of Theorem 1.2; that outer assembly (its Sections 3–5) is not attempted here, since it requires the preprint's own affine Steinberg-group construction and is out of scope for this submission.
-- source:
--   OpenAI, *Finite algebraic envelopes and the Boone–Higman conjecture*, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf, Lemma 2.1, p. 3.

import Mathlib
import Definitions.Def_BooneHigman

namespace OAI
namespace FiniteAlgebraicEnvelopes

universe u

theorem lemma_2_1_v2 {H : Type u} [Group H] [Group.FG H] (hH : HasDecidableWordProblem H) :
    ∃ (K : Type u) (_ : Group K), Group.FG K ∧ HasDecidableWordProblem K ∧
      ∃ (ι : H × H →* K), Function.Injective ι ∧
      ∃ s : K, ∀ g : H, ι (g, g) * s * (ι (g, g))⁻¹ * s⁻¹ = ι (g, 1) := by
  sorry

end FiniteAlgebraicEnvelopes
end OAI
