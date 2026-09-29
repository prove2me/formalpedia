-- Prove2me | Theorems.Thm_NgoFL_lattice_base_change_bijective
-- name    : NgoFL.lattice_base_change_bijective
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T00:24:20.847772+00:00
-- url     : https://prove2.me/theorems/9b4388b1-e87a-41aa-bce8-2a32fdb4fee1
-- title:
--   1.12.5: at good characteristic two lattices agree after base change
-- statement:
--   Ngo compares the two cocharacter lattices $X_*(T_1)$ and $X_*(T_2)$ of a pair of isogenous root
--   data inside the single $\mathbb{Q}$-vector space identified by $\psi_*$, and calls a prime $p$
--   *good with respect to $\psi^*$* when it divides neither of the indices
--
--   $$ \bigl|X_*(T_1)/(X_*(T_1)\cap X_*(T_2))\bigr|, \qquad
--      \bigl|X_*(T_2)/(X_*(T_1)\cap X_*(T_2))\bigr| . $$
--
--   Over a base of good residue characteristic, $\psi^*$ then induces an isomorphism
--   $X_*(T_1)\otimes k \to X_*(T_2)\otimes k$, and this is what makes the canonical isomorphism
--   $\mathfrak{t}_1 \to \mathfrak{t}_2$ of Lemme 1.12.6 exist integrally rather than only
--   rationally.
--
--   The statement to prove is the underlying general fact. Let $\Lambda_1$ and $\Lambda_2$ be two
--   subgroups of an abelian group, and let $O$ be a commutative ring in which both indices above
--   are invertible. Then the inclusion $\Lambda_1 \cap \Lambda_2 \hookrightarrow \Lambda_1$ becomes
--   bijective after tensoring with $O$ over $\mathbb{Z}$. Applying this to each of the two lattices
--   and composing gives the required isomorphism $\Lambda_1 \otimes O \simeq \Lambda_2 \otimes O$.
--
--   The point is not merely that the quotient $\Lambda_1/(\Lambda_1\cap\Lambda_2)$ dies after base
--   change — that would only give surjectivity — but that its $\mathrm{Tor}$ term dies too, which is
--   where the invertibility of the index is used a second time.
-- source:
--   Bao Chau Ngo, *Le lemme fondamental pour les algebres de Lie*, Publications mathematiques de l'IHES 111 (2010), 1-169, DOI 10.1007/s10240-010-0026-7, p. 24, 1.12.5 (good primes with respect to $\psi^*$) and Lemme 1.12.6

import Mathlib
import Definitions.Def_NgoRootDatumIsogeny

namespace NgoFL

theorem lattice_base_change_bijective {V : Type*} [AddCommGroup V] (L₁ L₂ : AddSubgroup V)
    (O : Type*) [CommRing O] (h : IsGoodBase O L₁ L₂) :
    Function.Bijective
      (LinearMap.rTensor O
        (AddSubgroup.inclusion (inf_le_left : L₁ ⊓ L₂ ≤ L₁)).toIntLinearMap) := by sorry

end NgoFL
