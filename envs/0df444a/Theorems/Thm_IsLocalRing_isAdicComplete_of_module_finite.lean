-- Prove2me | Theorems.Thm_IsLocalRing_isAdicComplete_of_module_finite
-- name    : IsLocalRing.isAdicComplete_of_module_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/467c416a-d974-5750-a7ab-65d45a611d50
-- title:
--   Adic completeness of a module-finite local algebra
-- statement:
--   Let $\mathcal{O}$ be a commutative ring which is Noetherian and local, and assume $\mathcal{O}$ is adically complete with respect to its maximal ideal $\mathfrak{m}_{\mathcal{O}}$, i.e. it is Hausdorff (the intersection of the powers $\mathfrak{m}_{\mathcal{O}}^n$ is zero) and precomplete (every sequence compatible modulo the powers $\mathfrak{m}_{\mathcal{O}}^n$ has a limit) for the $\mathfrak{m}_{\mathcal{O}}$-adic filtration. Let $T$ be a commutative $\mathcal{O}$-algebra which is finite as an $\mathcal{O}$-module, which is itself a local ring, and whose structure map $\mathcal{O} \to T$ is a local homomorphism (the preimage of the non-units of $T$ consists of non-units of $\mathcal{O}$). The conclusion is that $T$ is adically complete for its own maximal ideal $\mathfrak{m}_T$: the $\mathfrak{m}_T$-adic filtration on $T$ is separated and every $\mathfrak{m}_T$-adically compatible sequence in $T$ admits a limit.
--
--   This is the standard statement that a module-finite local algebra over a complete Noetherian local ring is again a complete local ring, proved here in the form of Mathlib's `IsAdicComplete` predicate. It supplies the completeness half of the structure of complete Noetherian local $\mathcal{O}$-algebra for rings constructed by finite extension, and is used in the project when deforming or lifting over such algebras, for instance in the constructions of étale and adjoin-root local algebras over a complete base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_isAdicComplete_of_module_finite.lean

import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem IsLocalRing.isAdicComplete_of_module_finite {𝒪 : Type u} {T : Type v} [CommRing 𝒪] [IsNoetherianRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [IsLocalRing T] [IsLocalHom (algebraMap 𝒪 T)] : IsAdicComplete (IsLocalRing.maximalIdeal T) T := by sorry
