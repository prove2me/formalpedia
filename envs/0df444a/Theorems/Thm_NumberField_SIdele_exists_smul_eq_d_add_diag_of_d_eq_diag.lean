-- Prove2me | Theorems.Thm_NumberField_SIdele_exists_smul_eq_d_add_diag_of_d_eq_diag
-- name    : NumberField.SIdele.exists_smul_eq_d_add_diag_of_d_eq_diag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/4f120aef-a346-54c6-a2d3-fa4c3e2c8b64
-- title:
--   Torsion for S-idèle 2-cochains modulo S-units
-- statement:
--   Let $E \subseteq K$ be number fields with $K/E$ Galois, write $G = K \simeq_{\mathrm{alg}[E]} K$ for the Galois group, and let $S$ be a finite set of height-one primes of $\mathcal{O}_E$. Two $\mathbb{Z}[G]$-representations occur: [`NumberField.SIdele.obj E K S`](def/NumberField_SIdeleModule.html#L75), the product over the index set `Index E S` (the disjoint sum of the finite index `FiniteSIdele.Index E S` and the infinite places of $E$) of the fibres [`NumberField.SIdele.fibre E K S`](def/NumberField_SIdeleModule.html#L68), these being the coinduced modules of local units, respectively local integer units, along the inclusions of the decomposition groups at the finite places, and the coinduced modules of archimedean local units at the infinite places, with $G$ acting componentwise; and [`NumberField.SUnits.sUnitsRep E K S`](def/NumberField_SUnitsModule.html#L52), the subrepresentation of $\mathrm{Additive}\,K^\times$ cut out by the $S$-units, with [`NumberField.SIdele.diag E K S`](def/NumberField_SIdeleModule.html#L91) the morphism of representations assembled from the components `diagComponent`. Let $n$ be a natural number divisible by $\operatorname{card} G$, let $f_1$ be a function from $G^3$ to the $S$-units representation, and let $c$ be a function from $G^2$ to the $S$-idèle representation such that the inhomogeneous-cochain differential $d^{2,3}$ applied to $c$ equals $g \mapsto \mathrm{diag}(f_1(g))$. Then there exist $\omega : G^1 \to$ `SIdele.obj E K S` and $e : G^2 \to$ `sUnitsRep E K S` with $n \cdot c = d^{1,2}\omega + (g \mapsto \mathrm{diag}(e(g)))$, the scalar $n$ acting as an integer.
--
--   This is the statement that a $2$-cochain of $S$-idèles whose coboundary is diagonal, i.e. one that becomes a $2$-cocycle in the quotient of the $S$-idèles by the $S$-units, becomes a coboundary modulo diagonal terms after multiplication by any multiple of $|\mathrm{Gal}(K/E)|$, reflecting the fact that the cohomology of a finite group in positive degree is annihilated by the group order. It is the one-layer ingredient of the torsion transfer used by [`NumberField.LevelArith.exists_smul_eq_smul_add_d_add_diag_of_sIdele_coboundary_of_le`](thm.html#NumberField.LevelArith.exists_smul_eq_smul_add_d_add_diag_of_sIdele_coboundary_of_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SIdele_exists_smul_eq_d_add_diag_of_d_eq_diag.lean

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory

theorem NumberField.SIdele.exists_smul_eq_d_add_diag_of_d_eq_diag
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (n : ℕ) (hn : Nat.card (K ≃ₐ[E] K) ∣ n)
    (f₁ : (Fin 3 → (K ≃ₐ[E] K)) → NumberField.SUnits.sUnitsRep E K S)
    (c : (Fin 2 → (K ≃ₐ[E] K)) → NumberField.SIdele.obj E K S)
    (hc : ((groupCohomology.inhomogeneousCochains (NumberField.SIdele.obj E K S)).d 2 3).hom c =
      fun g => (NumberField.SIdele.diag E K S).hom (f₁ g)) :
    ∃ (ω : (Fin 1 → (K ≃ₐ[E] K)) → NumberField.SIdele.obj E K S) (e : (Fin 2 → (K ≃ₐ[E] K)) → NumberField.SUnits.sUnitsRep E K S),
      (n : ℤ) • c = ((groupCohomology.inhomogeneousCochains (NumberField.SIdele.obj E K S)).d 1 2).hom ω + fun g => (NumberField.SIdele.diag E K S).hom (e g) := by sorry
