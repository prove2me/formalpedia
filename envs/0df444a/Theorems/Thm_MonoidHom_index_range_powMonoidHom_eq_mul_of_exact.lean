-- Prove2me | Theorems.Thm_MonoidHom_index_range_powMonoidHom_eq_mul_of_exact
-- name    : MonoidHom.index_range_powMonoidHom_eq_mul_of_exact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/7d95842b-26ca-55e8-91a8-94e5c317ea59
-- title:
--   Multiplicativity of the n-th power index in an exact sequence
-- statement:
--   Let $G$, $U$ and $F$ be commutative groups, let $\iota : U \to G$ and $\varphi : G \to F$ be group homomorphisms with $\iota$ injective and $\varphi$ surjective, and assume exactness in the middle in the form $\operatorname{range}\iota = \ker\varphi$. Let $n$ be a natural number and assume that $F$ has no nontrivial $n$-torsion: every $x \in F$ with $x^{n} = 1$ equals $1$. Writing, for a commutative group $H$, $\operatorname{range}(\mathrm{powMonoidHom}\ n : H \to H)$ for the subgroup $H^{n}$ of $n$-th powers, the conclusion is the equality of indices
--   $$[G : G^{n}] = [F : F^{n}] \cdot [U : U^{n}],$$
--   where `Subgroup.index` is used throughout, so that an infinite index is recorded as $0$ and the identity is an identity of natural numbers (in particular it also holds, trivially or otherwise, when some of the indices are infinite). No finiteness or finite-generation hypothesis is imposed on $G$, $U$ or $F$.
--
--   This is the standard multiplicativity of the index of $n$-th powers along a short exact sequence $1 \to U \to G \to F \to 1$ of abelian groups with $F$ free of $n$-torsion. It is used in the computation of the index of $n$-th powers in the $S$-unit group of a number field ([`NumberField.natCard_sUnit_quotient_range_powMonoidHom`](thm.html#NumberField.natCard_sUnit_quotient_range_powMonoidHom)) and in the local units of an adic completion ([`NumberField.natCard_units_adicCompletion_quotient_range_powMonoidHom`](thm.html#NumberField.natCard_units_adicCompletion_quotient_range_powMonoidHom)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MonoidHom_index_range_powMonoidHom_eq_mul_of_exact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MonoidHom.index_range_powMonoidHom_eq_mul_of_exact {G U F : Type*} [CommGroup G] [CommGroup U]
    [CommGroup F] (ι : U →* G) (φ : G →* F) (hι : Function.Injective ι) (hφ : Function.Surjective φ)
    (hexact : ι.range = φ.ker) {n : ℕ} (hF : ∀ x : F, x ^ n = 1 → x = 1) :
    (powMonoidHom n : G →* G).range.index
      = (powMonoidHom n : F →* F).range.index * (powMonoidHom n : U →* U).range.index := by sorry
