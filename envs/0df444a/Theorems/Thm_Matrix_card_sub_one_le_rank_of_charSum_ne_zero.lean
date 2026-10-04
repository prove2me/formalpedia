-- Prove2me | Theorems.Thm_Matrix_card_sub_one_le_rank_of_charSum_ne_zero
-- name    : Matrix.card_sub_one_le_rank_of_charSum_ne_zero
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T08:59:32.585986+00:00
-- url     : https://prove2.me/theorems/4a12e2cd-7721-4527-9ac7-7f189e1a3f04
-- title:
--   Dedekind's group matrix has rank at least $|G| - 1$ when all nontrivial character sums are nonzero
-- statement:
--   This is the rank form of Dedekind's group determinant for a finite abelian group.
--
--   Let $G$ be a finite abelian group of order $n$, and let $F$ be a field that contains a primitive $n$-th root of unity (so that the group of $n$-th roots of unity of $F$ is cyclic of order $n$ and the characters $\chi : G \to F^\times$ number exactly $n$). For a function $f : G \to F$ form the group matrix
--   $$A_f = \bigl(f(\sigma\tau^{-1})\bigr)_{\sigma,\tau \in G} \in F^{G \times G}.$$
--   For a character $\chi$ of $G$ with values in $F^\times$, the vector $(\chi(\tau))_{\tau \in G}$ is an eigenvector of $A_f$ with eigenvalue the character sum $\sum_{\rho \in G} \chi(\rho)^{-1} f(\rho)$; Dedekind's formula $\det A_f = \prod_\chi \sum_\rho \chi(\rho) f(\rho)$ is the determinant form of this decomposition. The statement here is the consequence for the rank:
--
--   > If the character sum $\displaystyle\sum_{\sigma \in G} \chi(\sigma)\, f(\sigma)$ is nonzero for every nontrivial character $\chi$ of $G$, then
--   > $$\operatorname{rank}_F A_f \;\ge\; n - 1.$$
--
--   The trivial character is excluded on purpose: its character sum $\sum_\sigma f(\sigma)$ may vanish, and it does vanish in the intended application (logarithms of the Galois conjugates of a unit, whose sum is the logarithm of a norm). The bound $n - 1$ is therefore the right one.
--
--   **Use.** In the proof of Leopoldt's conjecture for abelian fields, $G$ is the Galois group, $f(\sigma) = \log_p(\sigma\varepsilon)$ for a Minkowski unit $\varepsilon$, and the nonvanishing of the nontrivial character sums is Brumer's theorem; the rank bound then gives $n - 1 = \operatorname{rank}\mathcal{O}_K^\times$ independent rows. See `Leopoldt.charSum_log_ne_zero_of_brumer` and `Leopoldt.exists_linearIndependent_log_conj_of_card_sub_one_le_rank`.
--
--   **Formalization Note.** $G$ is a `Group` with `IsMulCommutative`, matching the Galois group `K ≃ₐ[ℚ] K` of an abelian extension; a proof may build a local `CommGroup` instance. The roots-of-unity hypothesis is Mathlib's `HasEnoughRootsOfUnity F (Fintype.card G)`; it implies that the characteristic of $F$ does not divide $n$, and with `HasEnoughRootsOfUnity.of_dvd` and `Monoid.exponent_dvd_card` it gives `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`, the count of characters. Characters are `G →* Fˣ` and are linearly independent by `linearIndependent_monoidHom`. The matrix is `Matrix.of fun σ τ => f (σ * τ⁻¹)` and the rank is `Matrix.rank` over $F$; the subtraction $n - 1$ is truncated natural-number subtraction, which is harmless since $n \ge 1$.
-- source:
--   Rank form of Dedekind's group determinant $\det(f(\sigma\tau^{-1}))_{\sigma,\tau} = \prod_{\chi} \sum_{\sigma} \chi(\sigma) f(\sigma)$ for a finite abelian group: L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Springer 1997, Section 5.5, Lemma 5.26 (group determinant); K. Conrad, The origin of representation theory, L'Enseignement Mathematique 44 (1998), 361-392 (Dedekind's factorization of the group determinant for abelian groups). The rank statement follows from the eigenvector decomposition: the character vectors $(\chi(\tau))_\tau$ are $|G|$ linearly independent eigenvectors with eigenvalues the character sums. Stated over a field with a primitive $|G|$-th root of unity (`HasEnoughRootsOfUnity`), excluding the trivial character.

import Mathlib

theorem Matrix.card_sub_one_le_rank_of_charSum_ne_zero
    {G : Type*} [Group G] [IsMulCommutative G] [Fintype G]
    {F : Type*} [Field F] [HasEnoughRootsOfUnity F (Fintype.card G)]
    (f : G → F)
    (hf : ∀ χ : G →* Fˣ, χ ≠ 1 → ∑ σ, ((χ σ : Fˣ) : F) * f σ ≠ 0) :
    Fintype.card G - 1 ≤ (Matrix.of fun σ τ : G => f (σ * τ⁻¹)).rank := by sorry
