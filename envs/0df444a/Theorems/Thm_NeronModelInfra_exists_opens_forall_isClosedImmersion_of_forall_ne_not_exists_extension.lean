-- Prove2me | Theorems.Thm_NeronModelInfra_exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension
-- name    : NeronModelInfra.exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/046d433c-d9f8-5e3e-89b5-1703ee46cce2
-- title:
--   Shrinking inequivalent smooth models so diagonals become closed immersions
-- statement:
--   Let $R$ be a discrete valuation ring with fraction field $K$, and let $g_K : X_K \to \operatorname{Spec} K$ be a separated, locally of finite type, quasi-compact $K$-scheme. Let $\iota$ be a finite index type and, for each $i$, let $f_i : Y_i \to \operatorname{Spec} R$ be smooth, separated, locally of finite type and quasi-compact, where $\operatorname{Spec} K \to \operatorname{Spec} R$ is the morphism induced by the structure map $R \to K$. Assume given, for each $i$, a morphism $e_i$ from the generic fibre $Y_i \times_{\operatorname{Spec} R} \operatorname{Spec} K$ to $X_K$ commuting with the projections to $\operatorname{Spec} K$ (i.e. a $K$-morphism), which is an isomorphism, and a point $\xi_i \in Y_i$ lying over the closed point of $\operatorname{Spec} R$ such that every point of $Y_i$ over the closed point lies in the closure of $\{\xi_i\}$. Assume the models are pairwise inequivalent near the $\xi_i$: for $i \neq j$, for every open $U \subseteq Y_i$ with $\xi_i \in U$ and every $R$-morphism $u : U \to Y_j$, the composite of the generic-fibre restriction of $u$ with $e_j$ differs from the composite of the generic-fibre restriction of the inclusion $U \hookrightarrow Y_i$ with $e_i$ as morphisms $U_K \to X_K$. Then there exist opens $V_i \subseteq Y_i$ such that: $\xi_i \in V_i$; every point of $Y_i$ not lying over the closed point belongs to $V_i$; the generic-fibre restriction $(V_i)_K \to (Y_i)_K$ of the inclusion is an isomorphism; and for $i \neq j$, every morphism $\delta$ from the fibre product of $(V_i)_K \to X_K$ and $(V_j)_K \to X_K$ (the maps obtained by composing the generic-fibre restrictions of the inclusions with $e_i$, resp. $e_j$) to $V_i \times_{\operatorname{Spec} R} V_j$ whose two components are the projections of that fibre product followed by the structure maps $(V_i)_K \to V_i$ and $(V_j)_K \to V_j$ is a closed immersion.
--
--   This is the shrinking step in the construction of a Néron model by gluing finitely many pairwise inequivalent smooth $R$-models of $X_K$: after replacing each $Y_i$ by a suitable open $V_i$ containing $\xi_i$ and the whole generic fibre, the condition that the generic-fibre diagonals $(V_i)_K \times_{X_K} (V_j)_K \to V_i \times_R V_j$ be closed immersions (Bosch–Lütkebohmert–Raynaud's condition $(*)$) holds for all $i \neq j$. It is used by [`NeronModelInfra.exists_model_openCover_of_forall_ne_not_exists_extension`](thm.html#NeronModelInfra.exists_model_openCover_of_forall_ne_not_exists_extension), and its proof cites [`NeronModelInfra.not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension`](thm.html#NeronModelInfra.not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open NeronModelInfra

universe u

theorem NeronModelInfra.exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {ι : Type u} [Finite ι]
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
    (hf : ∀ i, Smooth (f i) ∧ IsSeparated (f i) ∧ LocallyOfFiniteType (f i) ∧ QuasiCompact (f i))
    (e : ∀ i, SchemeHomOver (pullback.snd (f i) (specGenericFibreInclusion R K)) gK) (he : ∀ i, IsIso (e i).1)
    (ξ : ∀ i, ↥(Y i)) (hξ : ∀ i, (f i).base (ξ i) = IsLocalRing.closedPoint R)
    (hξgen : ∀ i (y : ↥(Y i)), (f i).base y = IsLocalRing.closedPoint R → ξ i ⤳ y)
    (hne : ∀ i j, i ≠ j → ∀ (U : (Y i).Opens), ξ i ∈ U → ∀ u : SchemeHomOver (U.ι ≫ f i) (f j),
      (genericFibreRestrict R K (f j) (U.ι ≫ f i) u).1 ≫ (e j).1 ≠
        (genericFibreRestrict R K (f i) (U.ι ≫ f i) ⟨U.ι, rfl⟩).1 ≫ (e i).1) :
    ∃ V : ∀ i, (Y i).Opens,
      (∀ i, ξ i ∈ V i) ∧
      (∀ i (y : ↥(Y i)), (f i).base y ≠ IsLocalRing.closedPoint R → y ∈ V i) ∧
      (∀ i, IsIso (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1) ∧
      ∀ i j, i ≠ j →
        ∀ δ : pullback
              (schemeHomOverComp (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩) (e i)).1
              (schemeHomOverComp (genericFibreRestrict R K (f j) ((V j).ι ≫ f j) ⟨(V j).ι, rfl⟩) (e j)).1 ⟶
            pullback ((V i).ι ≫ f i) ((V j).ι ≫ f j),
          δ ≫ pullback.fst ((V i).ι ≫ f i) ((V j).ι ≫ f j) =
            pullback.fst _ _ ≫ pullback.fst ((V i).ι ≫ f i) (specGenericFibreInclusion R K) →
          δ ≫ pullback.snd ((V i).ι ≫ f i) ((V j).ι ≫ f j) =
            pullback.snd _ _ ≫ pullback.fst ((V j).ι ≫ f j) (specGenericFibreInclusion R K) →
          IsClosedImmersion δ := by sorry
