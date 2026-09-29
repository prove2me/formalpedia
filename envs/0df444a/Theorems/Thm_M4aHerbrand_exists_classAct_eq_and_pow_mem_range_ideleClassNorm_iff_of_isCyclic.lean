-- Prove2me | Theorems.Thm_M4aHerbrand_exists_classAct_eq_and_pow_mem_range_ideleClassNorm_iff_of_isCyclic
-- name    : M4aHerbrand.exists_classAct_eq_and_pow_mem_range_ideleClassNorm_iff_of_isCyclic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/a23378cb-5cc7-5fdb-a860-84d71aea98d8
-- title:
--   Invariant idèle class of exact order [F:E] modulo norms
-- statement:
--   Let $E$ and $F$ be number fields with $F$ a Galois extension of $E$ whose Galois group $F \simeq_{\mathrm{alg}[E]} F$ is cyclic, and let $D$ be a datum `IdeleGaloisDescent (𝓞 F) E F`, that is: a monoid homomorphism $g \mapsto D.\mathrm{act}\,g$ from the Galois group to the ring automorphisms of the adèle ring `AdeleRing (𝓞 F) F`, such that $D.\mathrm{act}\,g$ carries the image of $x \in F$ under the structure map to the image of $g(x)$, and such that each $D.\mathrm{act}\,g$ is continuous. Write $C_F$ for `IdeleClassGroup (𝓞 F) F`, the quotient of the unit group $(\mathrm{AdeleRing}\,(𝓞 F)\,F)^\times$ by `principalIdeles`, the image of $F^\times$ under the induced map on units; $D$ induces on units the automorphisms `unitsAct` and hence endomorphisms $\mathrm{classAct}\,g$ of $C_F$, and `ideleClassNorm D` is the endomorphism $c \mapsto \prod_{\tau} \mathrm{classAct}\,\tau\,c$ over all $\tau$ in the Galois group. The assertion is that there exists $c \in C_F$ with $\mathrm{classAct}\,g\,c = c$ for every $g$, and such that for every natural number $k$ one has $c^k$ in the range of `ideleClassNorm D` if and only if the cardinality of the Galois group divides $k$.
--
--   This is the form of Artin reciprocity for a cyclic layer used in the construction of fundamental classes: the class of $c$ has order exactly $[F:E]$ in $\hat H^0$ of the Galois group acting on the idèle class group, i.e. in the invariants modulo norms. It is cited in the construction producing an element of the idèle class group of additive order equal to the degree together with a generation statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_classAct_eq_and_pow_mem_range_ideleClassNorm_iff_of_isCyclic.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField M4aHerbrand

theorem M4aHerbrand.exists_classAct_eq_and_pow_mem_range_ideleClassNorm_iff_of_isCyclic
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsCyclic (F ≃ₐ[E] F)] (D : IdeleGaloisDescent (𝓞 F) E F) :
    ∃ c : IdeleClassGroup (𝓞 F) F, (∀ g : F ≃ₐ[E] F, D.classAct g c = c) ∧
      ∀ k : ℕ, c ^ k ∈ (ideleClassNorm D).range ↔ Nat.card (F ≃ₐ[E] F) ∣ k := by sorry
