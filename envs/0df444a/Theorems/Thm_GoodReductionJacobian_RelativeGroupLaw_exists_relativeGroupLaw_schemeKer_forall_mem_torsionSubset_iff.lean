-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/cc5e3a5f-a0fb-5a0a-9569-ed5b69f6f580
-- title:
--   The n-kernel of a commutative relative group law
-- statement:
--   Let $R$ be a commutative ring and $f\colon J\to\operatorname{Spec}R$ a scheme over $R$, and let $L$ be a `RelativeGroupLaw R f`: a multiplication, unit and inverse on the set $\mathrm{SchemeHomOver}\ t\ f=\{\varphi : T\to J \mid \varphi\circ f=t\}$ for every $t\colon T\to\operatorname{Spec}R$, satisfying associativity, both unit laws, left inverse, and naturality under precomposition with $\psi\colon T'\to T$ over $\operatorname{Spec}R$. Assume the multiplication is commutative for every such $t$, and fix $n\in\mathbb N$. Write $[n]=$ `L.schemeNsmul n`$\colon J\to J$ for the underlying morphism of the $n$-fold multiple of the identity point $(\mathbf 1_J)$, $e\colon\operatorname{Spec}R\to J$ for the underlying morphism of the unit point over $\mathbf 1_{\operatorname{Spec}R}$, and $i=\mathrm{pr}_1\colon P=J\times_{[n],e}\operatorname{Spec}R\to J$. The assertion is that there exists a relative group law $L_K$ on $i$ followed by $f$ such that: $i$ followed by $f$ equals $\mathrm{pr}_2$, the structure map `L.schemeKerStr n`; $L_K$ is commutative; for all $t$ and $x,y$ over $t$, $(L_K.\mathrm{mul}\ t\ x\ y)$ followed by $i$ equals $L.\mathrm{mul}$ of $x$ followed by $i$ and $y$ followed by $i$; postcomposition with $i$ is injective on points over each $t$; and a point $x$ of $J$ over $t$ satisfies $L.\mathrm{nsmul}\ t\ n\ x=L.\mathrm{one}\ t$ exactly when $x=y$ followed by $i$ for some point $y$ of $P$ over $t$.
--
--   This is the statement that the kernel of multiplication by $n$ on a commutative relative group law is again a commutative relative group law, with $i\colon J[n]\to J$ a monomorphism on points whose image is the $n$-torsion subgroup of $J(T)$ for every $R$-scheme $T$. It is the input to the later analysis of $J[n]$: the Hopf-algebra description of its finite part over a henselian local ring, the Hecke-equivariant towers on $J_0(N)$, and the identification of kernel points with $n$-torsion of the group of sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff
    {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) :
    ∃ LK : RelativeGroupLaw R (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f),
      pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = L.schemeKerStr n ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
        LK.mul t x y = LK.mul t y x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
        NeronModelInfra.schemeHomOverComp (LK.mul t x y) (⟨pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        Function.Injective (fun y : SchemeHomOver t (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) =>
          NeronModelInfra.schemeHomOverComp y (⟨pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        x ∈ L.torsionSubset t n ↔
          ∃ y : SchemeHomOver t (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f), NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ = x) := by sorry
