-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_image_closedSubgroup_of_isFinite
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_image_closedSubgroup_of_isFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/ce29419e-ec30-5737-8932-81b3632408ae
-- title:
--   Image of a finite reduced subgroup scheme under a finite flat homomorphism
-- statement:
--   Let $k$ be an algebraically closed field and let $f_0 : A_0 \to \operatorname{Spec} k$, $f : A \to \operatorname{Spec} k$ be schemes over $k$, each equipped with a relative group law ($L_0$, resp. $L$): a functorial group structure on the sets $\{\varphi : T \to A_0 \mid \varphi \circ f_0 = t\}$, resp. for $f$, of points over an arbitrary $k$-scheme $t : T \to \operatorname{Spec} k$, with multiplication natural in $T$. Assume $f$ is separated and locally of finite type, and let $p : A_0 \to A$ satisfy $p$ followed by $f$ equals $f_0$, be a homomorphism on $T$-points for every $t$ (i.e. $p \circ (P \cdot_{L_0} Q) = (p \circ P) \cdot_L (p \circ Q)$), and be finite, flat and locally of finite presentation. Let $j : C \to A_0$ be a closed immersion with $C$ reduced and $j$ followed by $f_0$ finite, such that for every $t$ the unit $L_0.\mathrm{one}\,t$ factors through $j$ and the set of $t$-points factoring through $j$ is closed under $L_0$-multiplication and $L_0$-inversion (here a point $P$ factors through $j$ when $P$ equals some $T \to C$ followed by $j$). Then there exist a scheme $C'$ and $j' : C' \to A$ such that: $j'$ is a closed immersion, $j'$ followed by $f$ is finite, flat and locally of finite presentation, $C'$ is reduced, every unit $L.\mathrm{one}\,t$ factors through $j'$ and the points factoring through $j'$ are closed under $L$-multiplication and $L$-inversion; whenever $P$ factors through $j$, the point $p \circ P$ factors through $j'$; for every algebraically closed field $k'$, every ring homomorphism $sk : k \to k'$ and every point $Q$ over $\operatorname{Spec}(sk)$, $Q$ factors through $j'$ if and only if $Q = p \circ P$ for some point $P$ over $\operatorname{Spec}(sk)$ factoring through $j$; at every point $s$ of $\operatorname{Spec} k$ the rank $\mathrm{finrank}$ of $j'$ followed by $f$ equals the number of points over $\mathrm{id}_{\operatorname{Spec} k}$ factoring through $j'$; for every $m \in \mathbb{N}$, if the $m$-fold $L$-sum of $p \circ P$ is the unit for all $P$ factoring through $j$ (over all $T$), then the $m$-fold $L$-sum of every $Q$ factoring through $j'$ is the unit; and for all $e_0 : A_0 \to A_0$ over $f_0$ and $e : A \to A$ over $f$ with $e_0$ followed by $p$ equal to $p$ followed by $e$, if $e_0$ preserves factoring through $j$ on all $T$-points, then $e$ preserves factoring through $j'$ on all $T$-points.
--
--   This is the construction of the scheme-theoretic image $p(C)$ of a finite reduced closed subgroup scheme under a finite flat homomorphism of group schemes over an algebraically closed field, together with the properties of that image needed later: its geometric points are exactly the images of those of $C$, its degree equals its number of $k$-points, its exponent is controlled by that of $p(C)$ on points, and it inherits equivariance under endomorphisms compatible with $p$. It is used to transport level structures to quotients of fake elliptic curves, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny_of_levelLift`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny_of_levelLift).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_image_closedSubgroup_of_isFinite.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_image_closedSubgroup_of_isFinite
    {k : Type} [Field k] [IsAlgClosed k]
    {A₀ A : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of k)} {f : A ⟶ Spec (CommRingCat.of k)}
    (L₀ : RelativeGroupLaw k f₀) (L : RelativeGroupLaw k f)
    (hA_sep : IsSeparated f) (hA_lft : LocallyOfFiniteType f)
    (p : A₀ ⟶ A) (hp : p ≫ f = f₀)
    (hp_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f₀),
      mapPt p hp (L₀.mul t P Q) = L.mul t (mapPt p hp P) (mapPt p hp Q))
    (hp_finite : IsFinite p) (hp_flat : Flat p) (hp_fp : LocallyOfFinitePresentation p)
    (C : Scheme.{0}) (j : C ⟶ A₀) (hj_closed : IsClosedImmersion j) (hj_finite : IsFinite (j ≫ f₀)) (hC_red : IsReduced C)
    (hC_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough j (L₀.one t))
    (hC_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f₀),
      FactorsThrough j P → FactorsThrough j Q → FactorsThrough j (L₀.mul t P Q) ∧ FactorsThrough j (L₀.inv t P)) :
    ∃ (C' : Scheme.{0}) (j' : C' ⟶ A),
      IsClosedImmersion j' ∧ IsFinite (j' ≫ f) ∧ Flat (j' ≫ f) ∧ LocallyOfFinitePresentation (j' ≫ f) ∧ IsReduced C' ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough j' (L.one t)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
        FactorsThrough j' P → FactorsThrough j' Q → FactorsThrough j' (L.mul t P Q) ∧ FactorsThrough j' (L.inv t P)) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
        FactorsThrough j P → FactorsThrough j' (mapPt p hp P)) ∧

      (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k') (Q : SchemeHomOver (geomPoint k' sk) f),
        FactorsThrough j' Q ↔ ∃ P : SchemeHomOver (geomPoint k' sk) f₀, FactorsThrough j P ∧ mapPt p hp P = Q) ∧

      (∀ s : ↥(Spec (CommRingCat.of k)),
        (j' ≫ f).finrank s = Nat.card {Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f // FactorsThrough j' Q}) ∧

      (∀ m : ℕ, (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
          FactorsThrough j P → nsmulPt L t m (mapPt p hp P) = L.one t) →
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f),
          FactorsThrough j' Q → nsmulPt L t m Q = L.one t) ∧

      (∀ (e₀ : A₀ ⟶ A₀) (he₀ : e₀ ≫ f₀ = f₀) (e : A ⟶ A) (he : e ≫ f = f), e₀ ≫ p = p ≫ e →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
          FactorsThrough j P → FactorsThrough j (pushPt e₀ he₀ P)) →
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f),
          FactorsThrough j' Q → FactorsThrough j' (pushPt e he Q)) := by sorry
