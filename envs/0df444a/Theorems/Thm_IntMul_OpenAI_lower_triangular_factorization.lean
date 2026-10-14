-- Prove2me | Theorems.Thm_IntMul_OpenAI_lower_triangular_factorization
-- name    : IntMul.OpenAI.lower_triangular_factorization
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T13:50:08.453643+00:00
-- url     : https://prove2.me/theorems/51e8598b-47fd-41ad-81e5-90bf8017ff79
-- title:
--   Lower-triangular Bruhat factorization of a square matrix
-- statement:
--   Let $K$ be a field and $A$ an $m\times m$ matrix over $K$ of rank $a$. Then there is a factorization
--   $$A = E_1\,\Pi\,E_2,$$
--   where $E_1,E_2$ are lower triangular with nonzero diagonal entries (hence invertible), and $\Pi$ is a partial permutation matrix. That is, every entry of $\Pi$ is $0$ or $1$, each row and each column contains at most one $1$, and $\Pi$ has exactly $a$ entries equal to $1$.
--
--   This is Lemma 9 of the OpenAI preprint *Integer multiplication below $n\log n$*. It is the Bruhat factorization of a possibly singular matrix with the coordinate order reversed (Grigor'ev, Proposition 14(c)), arranged so that both triangular factors act on tape fields in the direction a streaming pass can update. In Lemma 10 of the preprint it turns a rational address shear $(H,D)\mapsto(H+AD,D)$ into exactly $\operatorname{rank}A$ interchanges of digit fields plus linear work. This is the source of the rank saving behind every $\kappa>0$ bound in the campaign.
--
--   **Formalization Note** "Lower triangular" means $E_{ij}=0$ for $i<j$ in the order of `Fin m`. The paper states the result over $\mathbb Q$; here it is stated over any field.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026 , Lemma 9 (Section 4.1); D. Grigor'ev, Appendix A.2, Proposition 14(c)

import Mathlib

namespace IntMul.OpenAI

theorem lower_triangular_factorization {m : ℕ} {K : Type*} [Field K] [DecidableEq K]
    (A : Matrix (Fin m) (Fin m) K) :
    ∃ E₁ P E₂ : Matrix (Fin m) (Fin m) K,
      (∀ i j, i < j → E₁ i j = 0) ∧ (∀ i, E₁ i i ≠ 0) ∧
      (∀ i j, i < j → E₂ i j = 0) ∧ (∀ i, E₂ i i ≠ 0) ∧
      (∀ i j, P i j = 0 ∨ P i j = 1) ∧
      (∀ i j j', P i j = 1 → P i j' = 1 → j = j') ∧
      (∀ i i' j, P i j = 1 → P i' j = 1 → i = i') ∧
      (Finset.univ.filter fun x : Fin m × Fin m => P x.1 x.2 = 1).card = A.rank ∧
      A = E₁ * P * E₂ := by sorry

end IntMul.OpenAI
