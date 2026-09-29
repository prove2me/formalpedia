-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_isIntegral_and_isLocallyNoetherian_and_forall_stalk_pullback_igusaTo_specMap_rat
-- name    : ModularCurve.IgusaScheme.isIntegral_and_isLocallyNoetherian_and_forall_stalk_pullback_igusaTo_specMap_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/c8001383-b601-5a20-a97c-6d673a151322
-- title:
--   The generic fibre of the Igusa scheme is Dedekind
-- statement:
--   Let $N \ge 1$ and let $q$ be a prime. Write $\mathbb{Z}_{(q)}$ for the base ring `R q`, which for the statement to typecheck is the subring [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ over which the Igusa scheme is built: [`ModularCurve.IgusaScheme N q`](def/ModularCurve_IgusaScheme.html#L255) is the pushout of the two morphisms `fFin N q`, `fInf N q` of affine schemes attached to the two chart algebras `chartAlgFin N q`, `chartAlgInf N q` inside the full modular function field of level $N$, and `IgusaScheme.igusaTo N q` is the morphism to $\operatorname{Spec} \mathbb{Z}_{(q)}$ obtained from the two structure maps of these chart algebras by the universal property of the pushout. Let $X$ be the fibre product of `igusaTo N q` with the morphism $\operatorname{Spec}\mathbb{Q} \to \operatorname{Spec}\mathbb{Z}_{(q)}$ induced by the inclusion, that is, the generic fibre. The conclusion is a fourfold conjunction: $X$ is an integral scheme; $X$ is locally Noetherian; for every point $y$ of $X$ the stalk $\mathcal{O}_{X,y}$ is integrally closed in its fraction field; and for every point $y$ the Krull dimension of $\mathcal{O}_{X,y}$, as an element of the extended ordered type, is at most $1$.
--
--   This records that the generic fibre of the Igusa scheme of level $N$ over $\mathbb{Z}_{(q)}$ satisfies the defining conditions of a Dedekind scheme (integral, locally Noetherian, normal of dimension at most one at every point). It is the input for the divisor- and dimension-theoretic work on the modular curve at level $N$ in characteristic zero, and is used in the computations of ranks of spaces of sections and of localised stalk modules on the Igusa scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_isIntegral_and_isLocallyNoetherian_and_forall_stalk_pullback_igusaTo_specMap_rat.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.DRLevel AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.IgusaScheme.isIntegral_and_isLocallyNoetherian_and_forall_stalk_pullback_igusaTo_specMap_rat
    (N q : ℕ) [NeZero N] [Fact q.Prime] :
    IsIntegral (pullback (IgusaScheme.igusaTo N q) (specMap (R q) ℚ)) ∧
    IsLocallyNoetherian (pullback (IgusaScheme.igusaTo N q) (specMap (R q) ℚ)) ∧
    (∀ y : ↥(pullback (IgusaScheme.igusaTo N q) (specMap (R q) ℚ)),
      IsIntegrallyClosed ((pullback (IgusaScheme.igusaTo N q) (specMap (R q) ℚ)).presheaf.stalk y)) ∧
    (∀ y : ↥(pullback (IgusaScheme.igusaTo N q) (specMap (R q) ℚ)),
      ringKrullDim ((pullback (IgusaScheme.igusaTo N q) (specMap (R q) ℚ)).presheaf.stalk y) ≤ 1) := by sorry
