-- Prove2me | Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_theorem_1_2
-- name    : OAI.FiniteAlgebraicEnvelopes.theorem_1_2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-12T18:39:51.025284+00:00
-- url     : https://prove2.me/theorems/dfd04b4e-cf54-4a1a-afe5-b96e84f7b417
-- title:
--   Theorem 1.2 (a two-transitive envelope with f.g. stabilizers)
-- statement:
--   Every finitely generated group $G$ with decidable word problem embeds into a finitely presented group $\Gamma$ that admits a faithful, two-transitive action on a countably infinite set, with every point stabilizer of that action finitely generated.
--
--   Here "two-transitive" means: for all $a \ne b$ and $c \ne d$ in the acted-upon set, some element of $\Gamma$ carries $a$ to $c$ and $b$ to $d$ simultaneously (Mathlib's `MulAction.IsMultiplyPretransitive Γ X 2`); "faithful" means only the identity of $\Gamma$ fixes every point (`FaithfulSMul`).
--
--   This is the preprint's principal intermediate result. Its proof (Sections 3–5, using an auxiliary algebraic construction from Section 6, built in turn from a self-referential finite monoid presentation in Section 7 and Appendix A) constructs $\Gamma$ as a finitely presented mapping torus of an affine Steinberg-type group, acting on an infinite direct limit of a finite-dimensional module over a custom finitely presented but non-simple algebra $B$, via a simple subalgebra $A \subseteq B$ reached after one step of a fixed nonunital endomorphism $\varphi : B \to B$.
--
--   **Formalization Note** The theorem is stated exactly as the preprint's own Theorem 1.2; its proof is not attempted here. $G$ need not itself be finitely presented — only finitely generated with a word-problem decision procedure, matching `HasDecidableWordProblem`.
-- source:
--   OpenAI, *Finite algebraic envelopes and the Boone–Higman conjecture*, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf, Theorem 1.2, p. 2.

import Mathlib
import Definitions.Def_BooneHigman

open OAI.FiniteAlgebraicEnvelopes

namespace OAI

namespace FiniteAlgebraicEnvelopes

universe u

theorem theorem_1_2 {G : Type u} [Group G] (hG : HasDecidableWordProblem G) :
    ∃ (Γ : Type u) (_ : Group Γ), Group.IsFinitelyPresented Γ ∧
      (∃ φ : G →* Γ, Function.Injective φ) ∧
      ∃ (X : Type u) (_ : MulAction Γ X) (_ : FaithfulSMul Γ X),
        MulAction.IsMultiplyPretransitive Γ X 2 ∧ Infinite X ∧ Countable X ∧
        ∀ x : X, Group.FG (MulAction.stabilizer Γ x) := by
  sorry

end FiniteAlgebraicEnvelopes
end OAI
