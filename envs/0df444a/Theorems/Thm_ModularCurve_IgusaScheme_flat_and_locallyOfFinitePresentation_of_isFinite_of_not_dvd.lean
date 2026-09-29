-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_flat_and_locallyOfFinitePresentation_of_isFinite_of_not_dvd
-- name    : ModularCurve.IgusaScheme.flat_and_locallyOfFinitePresentation_of_isFinite_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/e4f93142-e5a8-5215-82a3-a3d9f01168d3
-- title:
--   Finite surjections between Igusa schemes of good reduction are flat
-- statement:
--   Let $q$ be a prime and let $M, M'$ be nonzero natural numbers with $q \nmid M$ and $q \nmid M'$. For a level $N$ and the prime $q$, [`ModularCurve.IgusaScheme N q`](def/ModularCurve_IgusaScheme.html#L255) is the scheme obtained as the pushout of the two morphisms `fFin N q` and `fInf N q` out of `XMid N q`, i.e. glued from the spectra of the two charts `chartAlgFin N q` and `chartAlgInf N q` (the subalgebras of the full modular function field generated over the base ring [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) by $j$, respectively by $j^{-1}$), and `IgusaScheme.igusaTo N q` is the morphism to $\operatorname{Spec}$ of [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) obtained from the two structure morphisms of these charts by the pushout property. The datum $\pi$ is an element of `SchemeHomOver (IgusaScheme.igusaTo M' q) (IgusaScheme.igusaTo M q)`, that is, a morphism of schemes $\pi.1 \colon$ `IgusaScheme M' q` $\to$ `IgusaScheme M q` together with the condition that $\pi.1$ followed by `igusaTo M q` equals `igusaTo M' q`. Assume $\pi.1$ is finite and that its underlying map of topological spaces is surjective. Then $\pi.1$ is flat and locally of finite presentation.
--
--   This is the form of 'miracle flatness' used on the Igusa models of the modular curves of levels $M'$ and $M$ away from the residue characteristic $q$: a finite surjection between two schemes smooth over the discrete valuation ring [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) is automatically finite locally free. It is used in the construction of Hecke degeneracy pairs, [`ModularCurve.DRModelPackageLevel.exists_heckeDegeneracyPair`](thm.html#ModularCurve.DRModelPackageLevel.exists_heckeDegeneracyPair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_flat_and_locallyOfFinitePresentation_of_isFinite_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits NeronModelInfra
open AlgebraicGeometry
open ModularCurve
open ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.flat_and_locallyOfFinitePresentation_of_isFinite_of_not_dvd
    (M M' q : ℕ) [NeZero M] [NeZero M'] [Fact q.Prime] (hqM : ¬ q ∣ M) (hqM' : ¬ q ∣ M')
    (π : SchemeHomOver (IgusaScheme.igusaTo M' q) (IgusaScheme.igusaTo M q)) [IsFinite π.1]
    (hsurj : Function.Surjective π.1.base) :
    Flat π.1 ∧ LocallyOfFinitePresentation π.1 := by sorry
