-- Prove2me | Theorems.Thm_M4aHerbrand_nonempty_tate_addEquiv_ideleClass
-- name    : M4aHerbrand.nonempty_tate_addEquiv_ideleClass
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/a4081a84-df6a-5f26-8717-e30305ad5840
-- title:
--   Tate ̂ H⁰, ̂ H⁻¹ of a cyclic group on idèle classes
-- statement:
--   Let $R$ be a Dedekind domain, $E$ and $F$ fields with $F$ the fraction field of $R$ (via the given $R$-algebra structure) and $F$ an $E$-algebra, and suppose the group $G = F \simeq_{\mathrm{alg}[E]} F$ of $E$-algebra automorphisms of $F$ is finite. Write $C =$ `IdeleClassGroup R F` for the quotient of the unit group $(\mathrm{AdeleRing}\,R\,F)^\times$ by the subgroup of principal idèles, i.e. the image of $F^\times$ under $\mathrm{algebraMap}$. Let $D$ be an `IdeleGaloisDescent`, that is, a monoid homomorphism $g \mapsto D.\mathrm{act}\,g$ from $G$ to the ring automorphisms of $\mathrm{AdeleRing}\,R\,F$, each continuous, commuting with $\mathrm{algebraMap}$ from $F$ in the sense $D.\mathrm{act}\,g\,(x) = g(x)$ on $F$; $D$ induces for each $g$ an endomorphism $D.\mathrm{classAct}\,g$ of $C$. Let $\sigma \in G$ be such that every element of $G$ lies in `Subgroup.zpowers σ`, and suppose a `MulDistribMulAction` of $G$ on $C$ is given with $g \bullet c = D.\mathrm{classAct}\,g\,c$ for all $g$, $c$. Put $\Delta =$ `ideleClassDerive D σ`, $c \mapsto (D.\mathrm{classAct}\,\sigma\,c)\,c^{-1}$, and $N =$ `ideleClassNorm D`, $c \mapsto \prod_{\tau \in G} D.\mathrm{classAct}\,\tau\,c$. Then, for the representation `Rep.ofMulDistribMulAction` attached to this action, there exist additive isomorphisms $\widehat H^0 \cong \mathrm{Additive}(\ker \Delta / \mathrm{range}\,N)$ and $\widehat H^{-1} \cong \mathrm{Additive}(\ker N / \mathrm{range}\,\Delta)$, where $\widehat H^0$ is the invariants modulo the range of the norm map factored through the coinvariants and $\widehat H^{-1}$ is the kernel of that norm map, and in each degree the corresponding `Nat.card`s are equal.
--
--   This identifies the Tate cohomology of a cyclic Galois group acting on the idèle class group with the classical Herbrand-type quotients $\ker\Delta/N(C)$ and $\ker N/\Delta(C)$, together with the equality of cardinalities used when counting. It is invoked in the computations of $H^1$ and $H^2$ of the idèle class group for cyclic, and in particular prime-order, Galois groups, and in the construction of idèle characters from norm-invariant data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_nonempty_tate_addEquiv_ideleClass.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxSynthPendingDepth 3
universe u v w

theorem M4aHerbrand.nonempty_tate_addEquiv_ideleClass
    {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
    [Algebra R F] [IsFractionRing R F] [Algebra E F] [Fintype (F ≃ₐ[E] F)]
    (D : M4aHerbrand.IdeleGaloisDescent R E F) (σ : F ≃ₐ[E] F) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
    [MulDistribMulAction (F ≃ₐ[E] F) (M4aHerbrand.IdeleClassGroup R F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : M4aHerbrand.IdeleClassGroup R F), g • c = D.classAct g c) :
    Nonempty ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (M4aHerbrand.IdeleClassGroup R F)).tateH0 ≃+
      Additive ((M4aHerbrand.ideleClassDerive D σ).ker ⧸
        (M4aHerbrand.ideleClassNorm D).range.subgroupOf (M4aHerbrand.ideleClassDerive D σ).ker)) ∧
    Nonempty ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (M4aHerbrand.IdeleClassGroup R F)).tateHneg1 ≃+
      Additive ((M4aHerbrand.ideleClassNorm D).ker ⧸
        (M4aHerbrand.ideleClassDerive D σ).range.subgroupOf (M4aHerbrand.ideleClassNorm D).ker)) ∧
    Nat.card (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (M4aHerbrand.IdeleClassGroup R F)).tateH0 = Nat.card ((M4aHerbrand.ideleClassDerive D σ).ker ⧸
        (M4aHerbrand.ideleClassNorm D).range.subgroupOf (M4aHerbrand.ideleClassDerive D σ).ker) ∧
    Nat.card (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (M4aHerbrand.IdeleClassGroup R F)).tateHneg1 = Nat.card ((M4aHerbrand.ideleClassNorm D).ker ⧸
        (M4aHerbrand.ideleClassDerive D σ).range.subgroupOf (M4aHerbrand.ideleClassNorm D).ker) := by sorry
