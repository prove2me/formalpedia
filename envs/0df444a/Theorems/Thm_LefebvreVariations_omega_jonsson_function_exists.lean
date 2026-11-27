-- Prove2me | Theorems.Thm_LefebvreVariations_omega_jonsson_function_exists
-- name    : LefebvreVariations.omega_jonsson_function_exists
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:13:26.203131+00:00
-- url     : https://prove2.me/theorems/a07b557d-9001-536c-a45c-c724c791f426
-- title:
--   Lefebvre's variations, No. 245 — on a theme by Erdős and Hajnal: every infinite cardinal carries an omega-Jonsson function
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $\lambda$ be an infinite cardinal. Write $[\lambda]^\omega$ for the set of subsets of $\lambda$ of order type $\omega$ (countably infinite subsets). An *$\omega$-Jónsson function* on $\lambda$ is a function $f:[\lambda]^\omega\to\lambda$ such that $f``[A]^\omega=\lambda$ for every $A\subseteq\lambda$ with $|A|=\lambda$. Then, assuming the Axiom of Choice, every infinite cardinal $\lambda$ carries an $\omega$-Jónsson function; equivalently, there is no $\omega$-Jónsson cardinal.
--
--   This is the combinatorial half of Kunen's inconsistency theorem: for $\lambda=\sup_n j^n(\kappa)$ a nontrivial elementary $j:V\to V$ would make $\lambda$ an $\omega$-Jónsson cardinal.
--
--   **Formalization Note** The cardinal $\lambda$ is the cardinality of the infinite type `κ : Type u`. A countably infinite subset is `S : Set κ` with `S.Infinite ∧ S.Countable`; since the type of such sets is `[κ]^ω` (order type does not matter for the subset), `f : Set κ → κ` is any function, only its values on countably infinite sets being used. `A` has cardinality $\lambda$ as `Cardinal.mk A = Cardinal.mk κ`, and `f``[A]^ω = κ` is stated as surjectivity onto `κ` from the countably infinite subsets of `A`.
--
--   **Why this is a Lefebvre variation.** `KunenZF.kunen_inconsistency_zfc`, in its corrected nonempty form (the platform statement is false as formalized, since the empty structure is a model; verified disproof). Kunen's proof splits into this combinatorial theorem, which is about ordinary cardinals, and the argument that a nontrivial elementary $j:V\to V$ would make $\sup_n j^n(\kappa)$ an $\omega$-Jónsson cardinal. This statement is an ingredient of the base statement, not a special case. The second half of the proof has not been formalized, so the reduction is not Lean-verified.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). P. Erdős and A. Hajnal, On a problem of B. Jónsson, Bull. Acad. Polon. Sci. Sér. Sci. Math. Astronom. Phys. 14 (1966), 19–23; K. Kunen, Elementary embeddings and infinitary combinatorics, J. Symbolic Logic 36 (1971), 407–413 (there is no omega-Jonsson cardinal); A. Kanamori, The Higher Infinite, §23 (Kunen's inconsistency). Origin of this statement: it is the combinatorial ingredient of the standard proof of KunenZF.kunen_inconsistency_zfc (corrected nonempty form); the second half of that proof is not formalized, so the reduction is not Lean-verified.

import Mathlib

set_option autoImplicit false

universe u

namespace LefebvreVariations
theorem omega_jonsson_function_exists (κ : Type u) [Infinite κ] :
    ∃ f : Set κ → κ, ∀ A : Set κ, Cardinal.mk A = Cardinal.mk κ → ∀ b : κ,
      ∃ S : Set κ, S ⊆ A ∧ S.Infinite ∧ S.Countable ∧ f S = b := by sorry
end LefebvreVariations
