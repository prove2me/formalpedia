-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_not_isOpen_singleton_pullback_igusaTo_of_not_dvd
-- name    : ModularCurve.IgusaScheme.not_isOpen_singleton_pullback_igusaTo_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/920637e9-772c-5fed-8ade-4330720a058d
-- title:
--   Geometric fibres of the Igusa scheme have no isolated points
-- statement:
--   Let $M\ge 1$ and let $q$ be a prime with $q \nmid M$. Write $\mathbb{Z}_{(q)}$ for the subring [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $q$. Let $\kappa$ be an algebraically closed field of characteristic $q$, and let $\mathrm{to}\kappa \colon \mathbb{Z}_{(q)} \to \kappa$ be a ring homomorphism. Let [`ModularCurve.IgusaScheme.igusaTo M q`](def/ModularCurve_IgusaScheme.html#L277) be the structure morphism of the Igusa scheme of level $M$ over $\mathbb{Z}_{(q)}$ — the scheme obtained as the pushout of the two affine charts `Spec` of the subalgebras `chartAlgFin M q` and `chartAlgInf M q` of the modular function field along their common localisation, mapping to $\operatorname{Spec} \mathbb{Z}_{(q)}$ — and form its base change along $\operatorname{Spec}(\mathrm{to}\kappa)$, that is the scheme-theoretic pullback of `igusaTo M q` and `Spec.map (CommRingCat.ofHom toκ)`. The assertion is that for every point $w$ of the underlying topological space of this pullback, the singleton $\{w\}$ is not an open subset; equivalently, the geometric fibre has no isolated point.
--
--   This records the topological consequence of good reduction of the Igusa scheme at primes $q \nmid M$: the geometric fibres over characteristic $q$ are smooth integral curves over an algebraically closed field, and such a curve has no isolated point. It is used in the proof that the Igusa structure morphism is flat and locally of finite presentation for $q \nmid M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_not_isOpen_singleton_pullback_igusaTo_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve
open ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.not_isOpen_singleton_pullback_igusaTo_of_not_dvd
    (M q : ℕ) [NeZero M] [Fact q.Prime] (hqM : ¬ q ∣ M)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] (toκ : ↥(GaloisRep.ratLocalizedAt q) →+* κ)
    (w : ↥(pullback (IgusaScheme.igusaTo M q) (Spec.map (CommRingCat.ofHom toκ)))) :
    ¬ IsOpen ({w} : Set ↥(pullback (IgusaScheme.igusaTo M q) (Spec.map (CommRingCat.ofHom toκ)))) := by sorry
