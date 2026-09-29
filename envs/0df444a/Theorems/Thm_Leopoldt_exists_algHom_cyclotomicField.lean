-- Prove2me | Theorems.Thm_Leopoldt_exists_algHom_cyclotomicField
-- name    : Leopoldt.exists_algHom_cyclotomicField
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-09T15:35:35.608188+00:00
-- url     : https://prove2.me/theorems/e59142ea-f9fe-4a36-805c-ddc39eabcd46
-- title:
--   Kronecker--Weber: an abelian field embeds in a cyclotomic field
-- statement:
--   **Kronecker-Weber theorem.** Let $\mathbb{K}$ be a number field that is an abelian Galois extension of $\mathbb{Q}$. Then there is an integer $n \ge 1$ and an embedding of $\mathbb{Q}$-algebras
--
--   $$\mathbb{K} \hookrightarrow \mathbb{Q}(\zeta_n),$$
--
--   that is, $\mathbb{K}$ is (isomorphic to) a subfield of a cyclotomic field.
--
--   The theorem is the reason the abelian case of Leopoldt's conjecture reduces to the cyclotomic one: a vanishing Leopoldt defect passes to subfields, so Brumer's theorem for arbitrary abelian fields follows from the same statement for the fields $\mathbb{Q}(\zeta_n)$ alone. It is the first theorem of class field theory, the case of $\mathbb{Q}$ of the description of abelian extensions by ray class groups, and the subject of Hilbert's twelfth problem in general.
--
--   **Formalization note.** "Abelian Galois extension" is spelled with Mathlib's `IsGalois ℚ K` together with commutativity of $\mathrm{Gal}(\mathbb{K}/\mathbb{Q})$, matching the hypotheses of the mission's statement of Brumer's theorem, and $\mathbb{Q}(\zeta_n)$ is `CyclotomicField n ℚ`. The embedding is stated as `Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ)`, an unspecified $\mathbb{Q}$-algebra homomorphism, which is automatically injective. This theorem is not currently in Mathlib.
-- source:
--   The Kronecker-Weber theorem: every finite abelian extension of Q is contained in a cyclotomic field. Stated by L. Kronecker, "Ueber die algebraisch aufloesbaren Gleichungen", Berlin K. Akad. Wiss. (1853), 365-374 (his argument was incomplete for extensions of 2-power degree); a proof was published by H. Weber (1886), with gaps later corrected; the first complete proof is D. Hilbert, "Ein neuer Beweis des Kronecker'schen Fundamentalsatzes ueber Abel'sche Zahlkoerper", Nachrichten der Gesellschaft der Wissenschaften zu Goettingen (1896), 29-39. It is submitted here as the input needed to reduce Brumer's theorem, the mission's first milestone, to the cyclotomic case.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem exists_algHom_cyclotomicField (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    [IsMulCommutative (K ≃ₐ[ℚ] K)] :
    ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) := by sorry
end Leopoldt
