-- Prove2me | Theorems.Thm_NeronModelInfra_exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension
-- name    : NeronModelInfra.exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/aba349b9-cd4f-572b-a124-0642e06e8f99
-- title:
--   Néron smoothening over a discrete valuation ring
-- statement:
--   Let $R$ be a discrete valuation ring (a domain), let $K$ be a field that is an $R$-algebra and a fraction field of $R$, and write $\iota\colon \operatorname{Spec} K \to \operatorname{Spec} R$ for the morphism induced by the structure map $R \to K$ (this is `specGenericFibreInclusion R K`). Let $f\colon X \to \operatorname{Spec} R$ be a quasi-compact morphism of schemes that is locally of finite type, and assume the second projection $X \times_{\operatorname{Spec} R} \operatorname{Spec} K \to \operatorname{Spec} K$ of the pullback of $f$ along $\iota$ is smooth. Then there exist a scheme $X'$ and a morphism $u\colon X' \to X$ such that: the composite $u$ followed by $f$ is smooth and quasi-compact; $u$ is separated; the canonical comparison morphism on generic fibres $X' \times_{\operatorname{Spec} R} \operatorname{Spec} K \to X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ induced by $u$ and the identities on $\operatorname{Spec} K$ and $\operatorname{Spec} R$ is an isomorphism; and for every discrete valuation ring $R'$ (a domain) that is an $R$-algebra via a local homomorphism such that $\mathfrak m_R R' = \mathfrak m_{R'}$ and the residue field extension $\kappa(R) \to \kappa(R')$ is formally smooth, every morphism $x\colon \operatorname{Spec} R' \to X$ with $x$ followed by $f$ equal to $\operatorname{Spec}$ of $R \to R'$ factors as $x = x'$ followed by $u$ for some morphism $x'\colon \operatorname{Spec} R' \to X'$ satisfying the same compatibility over $\operatorname{Spec} R$.
--
--   This is Néron's smoothening process in the form used to produce weak Néron models: a quasi-compact, locally of finite type $R$-scheme with smooth generic fibre is dominated by a smooth quasi-compact one, by a separated morphism that is an isomorphism on generic fibres and through which all points with values in index-one extensions of $R$ lift. It is invoked in the construction of the Néron model property bundle for Jacobians of curves with good reduction over a henselian local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension.lean

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ (X' : Scheme.{u}) (u : X' ⟶ X),
      Smooth (u ≫ f) ∧ QuasiCompact (u ≫ f) ∧ IsSeparated u ∧
      IsIso (pullback.map (u ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) u
        (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) ∧
      ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          ∃ x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (u ≫ f), x'.1 ≫ u = x.1 := by sorry
