-- Prove2me | Theorems.Thm_Module_exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one
-- name    : Module.exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/dbab22ab-8c44-5906-a14d-fd9529bfbc89
-- title:
--   Local freeness near a point with integrally closed local ring of dimension ≤ 1
-- statement:
--   Let $A$ be a Noetherian commutative integral domain and $\mathfrak p \subset A$ a prime ideal such that the localisation $A_{\mathfrak p}$ (Lean's `Localization.AtPrime 𝔭`) is integrally closed in its fraction field and has Krull dimension at most $1$ (as an element of the extended natural/integer-valued dimension, `ringKrullDim (Localization.AtPrime 𝔭) ≤ 1`). Let $B$ be an $A$-module which is finitely generated over $A$ and has no zero smul-divisors, i.e. $a \cdot b = 0$ with $a \in A$, $b \in B$ forces $a = 0$ or $b = 0$. The assertion is that there exists $f \in A$ with $f \notin \mathfrak p$ such that the localised module $B_f$, realised as `LocalizedModule (Submonoid.powers f) B`, is a free module over the localisation $A_f =$ `Localization.Away f`. No freeness or rank statement is made at $\mathfrak p$ itself, and the element $f$ is not asserted to be unique or canonical; the conclusion is existence of one basic open neighbourhood of $\mathfrak p$ on which $B$ becomes free.
--
--   This is the standard statement that a finitely generated torsion-free module over a Noetherian domain is free on a basic open neighbourhood of any point whose local ring is a field or a discrete valuation ring, i.e. that such a point lies in the (open) free locus. It is used in the proof of [`AlgebraicGeometry.exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite`](thm.html#AlgebraicGeometry.exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite), where a finite morphism onto a normal locally Noetherian integral scheme is shown to be finite locally free over an open set containing the relevant points of codimension at most one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Module.exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
    (h𝔭ic : IsIntegrallyClosed (Localization.AtPrime 𝔭)) (h𝔭dim : ringKrullDim (Localization.AtPrime 𝔭) ≤ 1)
    (B : Type u) [AddCommGroup B] [Module A B] [Module.Finite A B] [NoZeroSMulDivisors A B] :
    ∃ f : A, f ∉ 𝔭 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) B) := by sorry
