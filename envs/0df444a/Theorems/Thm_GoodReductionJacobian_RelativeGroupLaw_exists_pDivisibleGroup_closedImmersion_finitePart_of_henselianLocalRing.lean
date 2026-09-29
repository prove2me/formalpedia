-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/052002c7-38c0-59d0-b234-64f8a0e041a6
-- title:
--   Finite parts of p-power torsion form a p-divisible group
-- statement:
--   Let $R$ be a henselian local ring, let $f\colon X \to \operatorname{Spec} R$ be separated and locally of finite type, let $L$ be a relative group law on $f$ (a functorial group structure on the sets $\{\varphi : T \to X \mid \varphi \circ f = t\}$ of points over each $t\colon T \to \operatorname{Spec} R$, natural in $T$), assume $L$ commutative, and let $p, h \in \mathbb{N}$. Write $X[n]$ for the pullback of `L.schemeNsmul n` (the morphism $X \to X$ given by the $n$-fold $L$-sum of the identity point) along the unit section, with structure morphism `L.schemeKerStr n` to $\operatorname{Spec} R$. Assume that for every $v$ the morphism $X[p^v] \to \operatorname{Spec} R$ is locally quasi-finite, quasi-compact and flat, and that for every $v$, every finite free $R$-algebra $H$ and every $R$-morphism $j\colon \operatorname{Spec} H \to X[p^v]$ that is simultaneously an open and a closed immersion and whose image contains every point of $X[p^v]$ lying over the closed point of $R$, one has $\operatorname{rank}_R H = p^{vh}$. Then there exist a $p$-divisible group $G$ over $R$ of parameters $p, h$ — a system of finite free cocommutative $R$-Hopf algebras $G_v =$ `G.level v` of rank $p^{vh}$ with surjective bialgebra transitions $i_v\colon G_{v+1} \to G_v$ whose kernels are the prescribed torsion ideals — together with morphisms $\iota_v\colon \operatorname{Spec} G_v \to X$ such that: each $\iota_v$ is a morphism over $\operatorname{Spec} R$; each $\iota_v$ is a closed immersion; $\iota_v$ followed by `L.schemeNsmul` $(p^v)$ is the unit section composed with the structure morphism; for every commutative $R$-algebra $B$ and all $x, y$ in the convolution group of $R$-algebra maps $G_v \to B$ whose associated morphisms $\operatorname{Spec} B \to X$ lie over $\operatorname{Spec} R$, the morphism attached to $x y$ is the $L$-product of those attached to $x$ and $y$; $\operatorname{Spec}(i_v)$ followed by $\iota_{v+1}$ equals $\iota_v$; every endomorphism $E$ of $X$ over $\operatorname{Spec} R$ that is compatible with $L$ on points is induced by a family of $R$-bialgebra endomorphisms $\varphi_v$ of $G_v$ commuting with the transitions, in the sense that $\operatorname{Spec}(\varphi_v)$ followed by $\iota_v$ equals $\iota_v$ followed by $E$; for each $v$ the induced morphism $\operatorname{Spec} G_v \to X[p^v]$ is both an open and a closed immersion and its image contains every point of $X[p^v]$ over the closed point of $R$; and for every module-finite $R$-algebra $T$, every $T$-valued point of $X$ over $\operatorname{Spec} R$ killed by $p^v$ for $L$ factors as $\operatorname{Spec}$ of an $R$-algebra map $G_v \to T$ followed by $\iota_v$.
--
--   This is the statement that, over a henselian local base, the finite parts of the $p$-power torsion kernels of a commutative group scheme assemble into a $p$-divisible group in the sense of Tate, embedded in the ambient scheme and receiving all module-finite-valued torsion points as well as all $L$-compatible endomorphisms; unlike the variant for finite $[p^v]$, here each $\operatorname{Spec} G_v \to X[p^v]$ is only an open and closed immersion containing the fibre over the closed point. The per-level Hopf-algebra input is [`GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing), and the result is applied to Néron models of Jacobians of modular curves in [`ModularCurve.exists_pDivisibleGroup_closedImmersion_finitePart_jHNeronObjectAtP_of_representsRelSubPic`](thm.html#ModularCurve.exists_pDivisibleGroup_closedImmersion_finitePart_jHNeronObjectAtP_of_representsRelSubPic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing
    {R : Type} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (p h : ℕ)
    (hlqf : ∀ v : ℕ, LocallyQuasiFinite (L.schemeKerStr (p ^ v)))
    (hqc : ∀ v : ℕ, QuasiCompact (L.schemeKerStr (p ^ v)))
    (hflat : ∀ v : ℕ, Flat (L.schemeKerStr (p ^ v)))

    (hrank : ∀ (v : ℕ) (H : Type) [CommRing H] [Algebra R H] [Module.Finite R H] [Module.Free R H]
      (j : Spec (CommRingCat.of H) ⟶ L.schemeKer (p ^ v)),
      j ≫ L.schemeKerStr (p ^ v) = Spec.map (CommRingCat.ofHom (algebraMap R H)) →
      IsOpenImmersion j → IsClosedImmersion j →
      (∀ x : ↥(L.schemeKer (p ^ v)), (L.schemeKerStr (p ^ v)).base x = IsLocalRing.closedPoint R →
        x ∈ Set.range j.base) →
      Module.finrank R H = p ^ (v * h)) :
    ∃ (G : PDivisibleGroup R p h) (ι : ∀ v : ℕ, Spec (CommRingCat.of (G.level v)) ⟶ X),

      (∀ v : ℕ, ι v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (G.level v)))) ∧

      (∀ v : ℕ, IsClosedImmersion (ι v)) ∧

      (∀ v : ℕ, ι v ≫ L.schemeNsmul (p ^ v) = (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ∧

      (∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R B] (x y : G.Point B v)
        (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
          Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
          Spec.map (CommRingCat.ofHom (algebraMap R B))),
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v =
          (L.mul (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟨_, hx⟩ ⟨_, hy⟩).1) ∧

      (∀ v : ℕ, Spec.map (CommRingCat.ofHom (G.transition v : G.level (v + 1) →+* G.level v)) ≫ ι (v + 1) = ι v) ∧

      (∀ (E : SchemeHomOver f f),
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) E =
            L.mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E)) →
        ∃ φ : ∀ v : ℕ, G.level v →ₐc[R] G.level v,
          (∀ v : ℕ, (G.transition v).comp (φ (v + 1)) = (φ v).comp (G.transition v)) ∧
          ∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : G.level v →+* G.level v)) ≫ ι v = ι v ≫ E.1) ∧

      (∀ (v : ℕ)
        (h3 : ι v ≫ L.schemeNsmul (p ^ v) = (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1),
        IsOpenImmersion (pullback.lift (f := L.schemeNsmul (p ^ v)) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
            (ι v) (ι v ≫ f) h3) ∧
        IsClosedImmersion (pullback.lift (f := L.schemeNsmul (p ^ v)) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
            (ι v) (ι v ≫ f) h3) ∧
        ∀ x : ↥(L.schemeKer (p ^ v)), (L.schemeKerStr (p ^ v)).base x = IsLocalRing.closedPoint R →
          x ∈ Set.range (pullback.lift (f := L.schemeNsmul (p ^ v)) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
            (ι v) (ι v ≫ f) h3).base) ∧

      (∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T]
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f),
        L.IsTorsionPoint _ (p ^ v) x →
        ∃ φ : G.level v →ₐ[R] T, Spec.map (CommRingCat.ofHom (φ : G.level v →+* T)) ≫ ι v = x.1) := by sorry
