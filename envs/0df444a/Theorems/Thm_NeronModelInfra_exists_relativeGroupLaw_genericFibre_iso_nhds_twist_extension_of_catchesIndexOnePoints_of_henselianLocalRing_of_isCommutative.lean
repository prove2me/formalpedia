-- Prove2me | Theorems.Thm_NeronModelInfra_exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative
-- name    : NeronModelInfra.exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/493e8175-ce53-55eb-99c8-4409476816e7
-- title:
--   Smooth group model with extending twisted translations (commutative case)
-- statement:
--   Let $R$ be a discrete valuation ring which is moreover a henselian local ring, with fraction field $K$, and let $g_K \colon X_K \to \operatorname{Spec} K$ be smooth, separated, locally of finite type and quasi-compact. Let $L_{X_K}$ be a relative group law on $g_K$, that is, a functorial group structure on the sets $\{\varphi \colon T \to X_K \mid \varphi \circ g_K = t\}$ of sections over each $K$-scheme $t \colon T \to \operatorname{Spec} K$, natural in $T$, and assume it is commutative on all such point sets. Let $M$ be a `ModelFamily`: a type $\iota$ of indices, assumed finite, schemes $X_i$ with structure morphisms $f_i \colon X_i \to \operatorname{Spec} R$, and for each $i$ a morphism $q_i$ from the generic fibre $X_i \times_{\operatorname{Spec} R} \operatorname{Spec} K$ to $X_K$ over $\operatorname{Spec} K$ whose underlying morphism is an open immersion; assume each $f_i$ is smooth, separated, locally of finite type and quasi-compact, and that $M$ catches index-one points: for every discrete valuation ring $R'$ that is a local $R$-algebra with fraction field $K'$, compatibly with $K$, such that the maximal ideal of $R$ generates the maximal ideal of $R'$ and the residue field extension is formally smooth, every $\operatorname{Spec} K'$-point of $X_K$ over $\operatorname{Spec} K$ is the generic fibre of an $R'$-point of some $X_i$ followed by $q_i$. Then there exist a scheme $B$, a morphism $g \colon B \to \operatorname{Spec} R$ that is smooth, separated, locally of finite type and quasi-compact, a relative group law $L_B$ on $g$, and a morphism $e$ from the generic fibre $B_K = B \times_{\operatorname{Spec} R} \operatorname{Spec} K$ to $X_K$ over $\operatorname{Spec} K$ whose underlying morphism is an isomorphism, such that: (i) $e$ is a homomorphism from the base change $L_B$ along $\operatorname{Spec} K \to \operatorname{Spec} R$ to $L_{X_K}$, i.e. for every $K$-scheme $t \colon T \to \operatorname{Spec} K$ and sections $x,y$ of $B_K$ over $t$, the product $x \cdot y$ for the generic fibre law followed by $e$ equals the $L_{X_K}$-product of $x$ followed by $e$ and $y$ followed by $e$; and (ii) twisted translations extend near maximal points of special fibres: for every smooth quasi-compact $z \colon Z \to \operatorname{Spec} R$, every section $u_K$ of $B_K$ over $Z_K$, and every point $\eta$ of $Z \times_{\operatorname{Spec} R} B$ lying over the closed point of $R$ and such that any point generalising $\eta$ and lying over the closed point equals $\eta$, there are an open $U \ni \eta$ of $Z \times_{\operatorname{Spec} R} B$ and a morphism $\tau \colon U \to B$ over $\operatorname{Spec} R$ whose generic fibre equals the base change of the inclusion $U \hookrightarrow Z \times_{\operatorname{Spec} R} B$ followed by the $L_B$-generic-fibre product of $u_K$ applied to the first projection and of the second projection, i.e. $(\zeta, x) \mapsto u_K(\zeta) \cdot x$ on $U_K$.
--
--   This is the passage from a weak Néron model of a smooth separated commutative group scheme of finite type over a henselian discrete valuation ring to a smooth separated finite-type group model whose twisted translations extend near the maximal points of the special fibre, the central step of the Bosch–Lütkebohmert–Raynaud construction of Néron models; the hypothesis of commutativity of the group law on all point sets is added to the general library statement. It is used in the construction of the Néron model property bundle for the generic fibre of an abelian scheme, and thence for Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_NeronModelInfra_WeakNeronModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK) (hcomm : LXK.IsCommutative)
    (M : ModelFamily R K gK) (hfin : Finite M.ι)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i))
    (hpts : M.CatchesIndexOnePoints) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (e : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧
      IsIso e.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e =
          LXK.mul t (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y e)) ∧
      (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K))
          (pullback.snd g (specGenericFibreInclusion R K)))
        (η : ↑(pullback z g)), (pullback.fst z g ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z g), y ⤳ η → (pullback.fst z g ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
        ∃ (U : (pullback z g).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z g ≫ z) g),
          (genericFibreRestrict R K g (U.ι ≫ pullback.fst z g ≫ z) τ).1 =
            pullback.map (U.ι ≫ pullback.fst z g ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z g ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              ((LB.genericFibre K).mul (pullback.snd (pullback.fst z g ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z g ≫ z) ⟨pullback.fst z g, rfl⟩) uK)
                (genericFibreRestrict R K g (pullback.fst z g ≫ z)
                  ⟨pullback.snd z g, pullback.condition.symm⟩)).1) := by sorry
