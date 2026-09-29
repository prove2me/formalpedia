-- Prove2me | Theorems.Thm_Leopoldt_exists_algHom_cyclotomicField_of_isCyclic_primePow
-- name    : Leopoldt.exists_algHom_cyclotomicField_of_isCyclic_primePow
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T02:48:31.474999+00:00
-- url     : https://prove2.me/theorems/880cec1c-da4c-414d-bfd1-f52218d201af
-- title:
--   Kronecker--Weber for cyclic extensions of prime-power degree
-- statement:
--   **Kronecker–Weber theorem, cyclic prime-power case.** Let $\mathbb{K}$ be a number field which is a Galois extension of $\mathbb{Q}$ whose Galois group $\mathrm{Gal}(\mathbb{K}/\mathbb{Q})$ is cyclic, and suppose $[\mathbb{K}:\mathbb{Q}] = p^k$ for a prime $p$ and some $k \ge 0$. Then there is an integer $n \ge 1$ and an embedding of $\mathbb{Q}$-algebras
--   $$\mathbb{K} \hookrightarrow \mathbb{Q}(\zeta_n).$$
--
--   This is the case to which the general Kronecker–Weber theorem is reduced in Washington's proof: a finite abelian group is a product of cyclic groups of prime-power order, so every abelian number field is the compositum of subfields with cyclic Galois group of prime-power order, and a compositum of subfields of cyclotomic fields lies in a cyclotomic field. The remaining (hard) work — reduction to extensions ramified only at $p$, and the analysis of those via ramification groups — is exactly the content of this statement. The cases $k \le 1$ with $p = 2$ (degree $\le 2$) are covered by `NumberField.exists_algHom_cyclotomicField_of_finrank_le_two`.
--
--   **Formalization note.** Galois is `IsGalois ℚ K`, cyclicity is `IsCyclic (K ≃ₐ[ℚ] K)`, the degree hypothesis is `Module.finrank ℚ K = p ^ k` with `p.Prime`, $\mathbb{Q}(\zeta_n)$ is `CyclotomicField n ℚ`, and the embedding is an unspecified `K →ₐ[ℚ] CyclotomicField n ℚ`.
-- source:
--   L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Chapter 14, Section 14.1, proof of Theorem 14.1: reduction to K/Q cyclic of degree p^m (then Lemmas 14.2-14.4 and the ramification argument). Kronecker-Weber: every finite abelian extension of Q is contained in a cyclotomic field.

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Basic

namespace Leopoldt
theorem exists_algHom_cyclotomicField_of_isCyclic_primePow (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] [IsCyclic (K ≃ₐ[ℚ] K)] (p k : ℕ) (hp : p.Prime)
    (hK : Module.finrank ℚ K = p ^ k) :
    ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) := by sorry
end Leopoldt
