-- Prove2me | Theorems.Thm_M4aHerbrand_ideleGaloisDescent_restrict_intermediateField
-- name    : M4aHerbrand.ideleGaloisDescent_restrict_intermediateField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/0b8897e3-ccf8-5a05-984d-b8ef3f874080
-- title:
--   Restriction of an idele Galois descent datum to an intermediate field
-- statement:
--   Let $R$ be a Dedekind domain, $E$ and $F$ fields with $F$ an $R$-algebra that is a fraction field of $R$ and an $E$-algebra, and write $\mathbb{A}_F$ for the adele ring `AdeleRing R F`. A datum `IdeleGaloisDescent R E F` consists of a monoid homomorphism $\mathrm{act} : (F \simeq_{\mathrm{alg}[E]} F) \to \mathrm{RingAut}(\mathbb{A}_F)$ such that $\mathrm{act}(g)$ commutes with the structure map $F \to \mathbb{A}_F$ in the sense that $\mathrm{act}(g)(\iota(x)) = \iota(g x)$ for all $x \in F$, and such that each $\mathrm{act}(g)$ is continuous. Given such a datum $D$ over $E$ and an intermediate field $E'$ of $F/E$, the theorem asserts three things: (1) for every datum $D'$ of type `IdeleGaloisDescent R E' F` and every $g : F \simeq_{\mathrm{alg}[E']} F$, one has $D'.\mathrm{act}\,g = D.\mathrm{act}\,(g$ restricted to scalars in $E)$ as ring automorphisms of $\mathbb{A}_F$; (2) for every such $D'$, every such $g$ and every class $c$ in the idele class group $\mathbb{A}_F^\times / \iota(F)^\times$ (the quotient of the units of $\mathbb{A}_F$ by the image of the units of $F$), the induced maps agree, $D'.\mathrm{classAct}\,g\,c = D.\mathrm{classAct}\,(g|_E)\,c$; and (3) the type `IdeleGaloisDescent R E' F` is nonempty.
--
--   This is the bookkeeping that makes a Galois descent datum for the ideles of $F$ over a base field functorial in the base: any datum over an intermediate field $E'$ necessarily acts through the given datum over $E$, and such a datum over $E'$ exists. It is used whenever a result proved for an arbitrary descent datum over $E'$ — for instance over the fixed field of a subgroup, in the cohomological computations with idele classes — has to be transported back to the fixed datum over $E$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_ideleGaloisDescent_restrict_intermediateField.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem M4aHerbrand.ideleGaloisDescent_restrict_intermediateField
    (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
    [Algebra R F] [IsFractionRing R F] [Algebra E F]
    (D : M4aHerbrand.IdeleGaloisDescent R E F) (E' : IntermediateField E F) :
    (∀ (D' : M4aHerbrand.IdeleGaloisDescent R E' F) (g : F ≃ₐ[E'] F),
        D'.act g = D.act (g.restrictScalars E)) ∧
    (∀ (D' : M4aHerbrand.IdeleGaloisDescent R E' F) (g : F ≃ₐ[E'] F)
        (c : M4aHerbrand.IdeleClassGroup R F),
        D'.classAct g c = D.classAct (g.restrictScalars E) c) ∧
    Nonempty (M4aHerbrand.IdeleGaloisDescent R E' F) := by sorry
