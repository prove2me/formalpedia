-- Prove2me | Theorems.Thm_LefebvreVariations_omega_jonsson_function_exists_cof_omega
-- name    : LefebvreVariations.omega_jonsson_function_exists_cof_omega
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:13:41.124001+00:00
-- url     : https://prove2.me/theorems/1f42de18-ee10-5ff8-bdc1-83c0beec9aeb
-- title:
--   Lefebvre's variations, No. 246 — on a theme by Erdős and Hajnal: every cardinal of countable cofinality carries an omega-Jonsson function
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $\lambda$ be an infinite cardinal of cofinality $\omega$ (for instance $\lambda=\aleph_\omega$, or $\lambda = \sup_n j^n(\kappa)$ in Kunen's argument). Write $[\lambda]^\omega$ for the countably infinite subsets of $\lambda$. Then, assuming the Axiom of Choice, there is a function $f:[\lambda]^\omega\to\lambda$ with $f``[A]^\omega=\lambda$ for every $A\subseteq\lambda$ with $|A|=\lambda$ (an $\omega$-Jónsson function).
--
--   This is the case of the Erdős–Hajnal–Kunen theorem that Kunen's inconsistency proof uses, since $\sup_n j^n(\kappa)$ has cofinality $\omega$. It is a special case of the statement for all infinite cardinals.
--
--   **Formalization Note** The cardinal $\lambda$ is the cardinality of the infinite type `κ : Type u`, and cofinality $\omega$ is `Ordinal.cof (Cardinal.mk κ).ord = Cardinal.aleph0`. A countably infinite subset is `S : Set κ` with `S.Infinite ∧ S.Countable`; `f : Set κ → κ` is any function, only its values on countably infinite sets being used. The conclusion says that for every `A` of cardinality `λ` the values of `f` on countably infinite subsets of `A` cover `κ`.
--
--   **Why this is a Lefebvre variation.** `KunenZF.kunen_inconsistency_zfc`, in its corrected nonempty form (the platform statement is false as formalized, since the empty structure is a model; verified disproof). In Kunen's proof the only cardinal at which an $\omega$-Jónsson function is needed is $\lambda=\sup_n j^n(\kappa)$, of cofinality $\omega$. This statement is that case, a special case of `omega_jonsson_function_exists` and an ingredient of the base statement. The second half of the proof has not been formalized, so the reduction is not Lean-verified.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). P. Erdős and A. Hajnal, On a problem of B. Jónsson, Bull. Acad. Polon. Sci. Sér. Sci. Math. Astronom. Phys. 14 (1966), 19–23; K. Kunen, Elementary embeddings and infinitary combinatorics, J. Symbolic Logic 36 (1971), 407–413; A. Kanamori, The Higher Infinite, §23. Origin of this statement: it is the combinatorial ingredient (cofinality omega case) of the standard proof of KunenZF.kunen_inconsistency_zfc (corrected nonempty form); the second half of that proof is not formalized, so the reduction is not Lean-verified.

import Mathlib

set_option autoImplicit false

universe u

namespace LefebvreVariations
theorem omega_jonsson_function_exists_cof_omega (κ : Type u) [Infinite κ]
    (hcof : Ordinal.cof (Cardinal.mk κ).ord = Cardinal.aleph0) :
    ∃ f : Set κ → κ, ∀ A : Set κ, Cardinal.mk A = Cardinal.mk κ → ∀ b : κ,
      ∃ S : Set κ, S ⊆ A ∧ S.Infinite ∧ S.Countable ∧ f S = b := by sorry
end LefebvreVariations
