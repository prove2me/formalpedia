-- Prove2me | Theorems.Thm_MinrankTW_eq_22_23
-- name    : MinrankTW.eq_22_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:56.595845+00:00
-- url     : https://prove2.me/theorems/246af0d9-2ad2-4ad2-a642-da04d5be1bca
-- title:
--   Eqs. (22)–(23) — $Z=CB$ and $T=BC^{\mathsf T}=C^{-1}ZC^{\mathsf T}=B(B^{\mathsf T})^{-1}Z^{\mathsf T}$
-- statement:
--   On tables indexed by the linear relations in $\mathbb F_q^a\oplus\mathbb F_q^c$ with values in a commutative ring, let $Z$ be the subspace zeta transform, $C$ and $B$ the restriction transforms (21) and $T$ the transform (19); a transpose is the transpose of the matrix of a transform. Then
--
--   1. $Z=CB$ (22);
--   2. $B$ and $C$ are invertible;
--   3. $T=BC^{\mathsf T}$;
--   4. $T=C^{-1}ZC^{\mathsf T}$;
--   5. $T=B(B^{\mathsf T})^{-1}Z^{\mathsf T}$ (23).
--
--   These factorizations reduce $T$ and its inverse to full and restricted subspace zeta transforms, which Theorem 4 computes fast.
--
--   **Formalization Note** Clause 4 is stated as $CT=ZC^{\mathsf T}$, and clause 5 as: whenever $B^{\mathsf T}g=Z^{\mathsf T}f$, $Tf=Bg$. Given clause 2 and the invertibility of $B^{\mathsf T}$ these are the displayed identities.
--
--   Differences from the source:
--   - encoding: T = C⁻¹ZCᵀ and T = B(Bᵀ)⁻¹Zᵀ → C ∘ T = Z ∘ Cᵀ, and Bᵀg = Zᵀf ⟹ Tf = Bg; reason: equivalent given that B, C (and hence Bᵀ) are invertible, which is clause 2
--   - reading: tables (value ring unspecified) → tables with values in an arbitrary commutative ring; reason: as in Lemma 2
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 4.3, p.14, Eqs. (21)–(23)

import Mathlib
import Definitions.Def_MinrankTW_tableMap
import Definitions.Def_MinrankTW_zetaKer
import Definitions.Def_MinrankTW_relTransforms

namespace MinrankTW

/-- **Eqs. (22)–(23)**, Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §4.3, p.14. As linear transforms on tables indexed by linear
relations in `F^a ⊕ F^c` (values in a commutative ring; a transpose is the transpose of the
matrix of the transform):
1. `Z = C B` (22);
2. `B` and `C` are invertible;
3. `T = B Cᵀ`;
4. `T = C⁻¹ Z Cᵀ`, stated as `C T = Z Cᵀ`;
5. `T = B (Bᵀ)⁻¹ Zᵀ`, stated as: if `Bᵀ g = Zᵀ f` then `T f = B g` (23).

**Formalization Note** `Z`, `C`, `B`, `T` are `tableMap` of their 0/1 matrices `zetaKer`,
`cKer`, `bKer`, `tKer`; the transpose of `tableMap k` is `tableMap (fun R S => k S R)`;
composition is composition of functions on tables. -/
theorem eq_22_23 {F : Type} [Field F] [Fintype F] {α γ : Type} [Fintype α] [Fintype γ]
    {A : Type} [CommRing A] :
    (∀ f : Submodule F ((α → F) × (γ → F)) → A,
      tableMap zetaKer f = tableMap cKer (tableMap bKer f)) ∧
    Function.Bijective (tableMap (bKer (F := F) (α := α) (γ := γ)) :
      (Submodule F ((α → F) × (γ → F)) → A) → Submodule F ((α → F) × (γ → F)) → A) ∧
    Function.Bijective (tableMap (cKer (F := F) (α := α) (γ := γ)) :
      (Submodule F ((α → F) × (γ → F)) → A) → Submodule F ((α → F) × (γ → F)) → A) ∧
    (∀ f : Submodule F ((α → F) × (γ → F)) → A,
      tableMap tKer f = tableMap bKer (tableMap (fun R Q => cKer Q R) f)) ∧
    (∀ f : Submodule F ((α → F) × (γ → F)) → A,
      tableMap cKer (tableMap tKer f) = tableMap zetaKer (tableMap (fun R Q => cKer Q R) f)) ∧
    (∀ f g : Submodule F ((α → F) × (γ → F)) → A,
      tableMap (fun R S => bKer S R) g = tableMap (fun R S => zetaKer S R) f →
        tableMap tKer f = tableMap bKer g) := by sorry

end MinrankTW
