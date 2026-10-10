-- Prove2me | Theorems.Thm_GGHRSW_ColoredMatrix_lemma_2
-- name    : GGHRSW.ColoredMatrix.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:06:53.133105+00:00
-- url     : https://prove2.me/theorems/b213e8d0-2052-4741-a8d8-a073a9506da5
-- title:
--   Lemma 2 (Straddling Lemma), p. 42 — for ∅ ⊊ I ⊊ [k], ∏_{i∈I} α_i and ∏_{i∈I′} α′_i are distinct multilinear monomials in the γ's
-- statement:
--   Fix an integer $k$ and formal variables $\gamma_1,\dots,\gamma_{2k}$. Set
--   $$\alpha_i = \gamma_{2i-1}\gamma_{2i},\qquad \alpha'_i = \gamma_{2i}\gamma_{2i+1}\qquad (i\in[k]),$$
--   with index arithmetic modulo $2k$. For any subsets $I,I'\subseteq[k]$ with $\emptyset\subsetneq I\subsetneq[k]$, the products
--   $$\prod_{i\in I}\alpha_i \quad\text{and}\quad \prod_{i\in I'}\alpha'_i$$
--   are multilinear monomials in $\gamma_1,\dots,\gamma_{2k}$, and they are distinct.
--
--   The bundling of the scalars along a block of steps is what prevents an adversary from combining an inconsistent assignment of a block in the primal program with any part of the dummy program; this lemma is the combinatorial core of that argument.
--
--   **Formalization Note.** Monomials are represented by their exponent vectors in $\mathbb N^{2k}$ (finitely supported functions on $\mathrm{Fin}(2k)$), with 0-based indices: $\gamma_{2i-1},\gamma_{2i}$ for $i\in[k]$ become coordinates $2i$ and $2i+1$ for $i\in\{0,\dots,k-1\}$, and $\gamma_{2i+1}$ becomes coordinate $(2i+2)\bmod 2k$. "Multilinear" is the statement that every exponent is at most $1$. The page's random drawing of the $\gamma$'s "$\leftarrow\mathbb Z_q$" plays no role in the statement, which is about formal monomials, and is omitted.
-- source:
--   Garg, Gentry, Halevi, Raykova, Sahai and Waters, Candidate Indistinguishability Obfuscation and Functional Encryption for All Circuits, SIAM J. Comput. 45(3), 2016 (authors' version of July 21, 2013), p. 42, Lemma 2 (Straddling Lemma)

import Mathlib

namespace GGHRSW.ColoredMatrix

theorem lemma_2 (k : ℕ) (I I' : Finset (Fin k)) (hI : I.Nonempty) (hIk : I ≠ Finset.univ) :
    let a : Fin (2 * k) →₀ ℕ := ∑ i ∈ I,
      (Finsupp.single (⟨2 * i.val, by omega⟩ : Fin (2 * k)) 1 +
        Finsupp.single (⟨2 * i.val + 1, by omega⟩ : Fin (2 * k)) 1)
    let a' : Fin (2 * k) →₀ ℕ := ∑ i ∈ I',
      (Finsupp.single (⟨2 * i.val + 1, by omega⟩ : Fin (2 * k)) 1 +
        Finsupp.single (⟨(2 * i.val + 2) % (2 * k), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2 * k)) 1)
    a ≠ a' ∧ (∀ x, a x ≤ 1) ∧ (∀ x, a' x ≤ 1) := by sorry

end GGHRSW.ColoredMatrix
