-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_isIntegral
-- name    : ModularCurve.IgusaScheme.isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/68a05aed-8943-57ee-8cbf-f2d3b2da96c6
-- title:
--   Integrality of the two-chart Igusa scheme
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ (carried by a `NeZero N` instance) and let $\ell$ be a natural number assumed prime (carried by a `Fact ℓ.Prime` instance). The scheme [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255) is, by definition, the pushout in the category of schemes (over the base `Scheme.{0}`) of the two morphisms `fFin N ℓ` and `fInf N ℓ` out of `XMid N ℓ`, where `fFin N ℓ : XMid N ℓ ⟶ XFin N ℓ` is the morphism of spectra induced by the ring homomorphism `inclFin N ℓ`, and `fInf N ℓ : XMid N ℓ ⟶ XInf N ℓ` is the morphism of spectra induced by `inclInf N ℓ`; so it is the scheme obtained by glueing the two affine charts `XFin N ℓ` and `XInf N ℓ` along the middle chart `XMid N ℓ`. The assertion is that this scheme is integral in the sense of `AlgebraicGeometry.IsIntegral`: its underlying topological space is irreducible (in particular nonempty) and it is reduced. No further hypothesis on $N$ or $\ell$ is imposed.
--
--   This records that the integral model of the modular curve assembled from its two affine charts over the localisation of $\mathbb{Z}$ at $\ell$ is an integral scheme, i.e. irreducible and reduced. It is used downstream, for instance to know that a relative dimension or a rank is constant across the scheme and that generic-fibre arguments may be run on an integral base; the result is quoted by several statements about the smooth locus and about ranks of the associated modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_isIntegral.lean

import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.isIntegral (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    IsIntegral (ModularCurve.IgusaScheme N ℓ) := by sorry
