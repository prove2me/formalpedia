-- Prove2me | Theorems.Thm_NeronModelInfra_finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
-- name    : NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/b19fb9aa-20a2-536d-9532-e320f1d5e159
-- title:
--   Maximal points of the special fibre of a smooth model over a DVR
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the discrete valuation ring property), let $Y$ be a scheme and let $f \colon Y \to \operatorname{Spec} R$ be smooth, locally of finite type and quasi-compact. Call $\xi \in Y$ *maximal special* if $f$ maps $\xi$ to the closed point of $\operatorname{Spec} R$ and every $y'$ lying over the closed point with $y' \rightsquigarrow \xi$ (that is, $\xi$ in the closure of $\{y'\}$) satisfies $y' = \xi$; equivalently, $\xi$ is a generic point of an irreducible component of the special fibre. The theorem asserts three things simultaneously. First, the set of maximal special points of $Y$ is finite. Second, for every $y \in Y$ lying over the closed point there is exactly one maximal special $\xi$ with $\xi \rightsquigarrow y$, i.e. $y$ lies in the closure of $\{\xi\}$. Third, for every maximal special $\xi$ there is an open subscheme $V \subseteq Y$ with $\xi \in V$, containing every point of $Y$ not lying over the closed point, and such that the points of $V$ over the closed point are precisely the points over the closed point lying in the closure of $\{\xi\}$ (both inclusions are stated separately).
--
--   This is the topological input on special fibres of smooth quasi-compact $R$-models used in the construction of weak Néron models: the special fibre is a noetherian sober space with finitely many irreducible components, and smoothness over the residue field makes these components pairwise disjoint, hence open and closed in the fibre and cut out by opens of $Y$ containing the whole generic fibre. It is invoked in the selection of minimal component data and in the construction of translation extensions by open immersions over a cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens.lean

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Set.Finite {ξ : Y | f.base ξ = IsLocalRing.closedPoint R ∧
        ∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ} ∧
    (∀ y : Y, f.base y = IsLocalRing.closedPoint R →
      ∃! ξ : Y, (f.base ξ = IsLocalRing.closedPoint R ∧
        (∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ)) ∧ ξ ⤳ y) ∧
    (∀ ξ : Y, f.base ξ = IsLocalRing.closedPoint R →
      (∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ) →
      ∃ V : Y.Opens, ξ ∈ V ∧ (∀ y' : Y, f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V) ∧
        (∀ y' : Y, y' ∈ V → f.base y' = IsLocalRing.closedPoint R → ξ ⤳ y') ∧
        (∀ y' : Y, f.base y' = IsLocalRing.closedPoint R → ξ ⤳ y' → y' ∈ V)) := by sorry
