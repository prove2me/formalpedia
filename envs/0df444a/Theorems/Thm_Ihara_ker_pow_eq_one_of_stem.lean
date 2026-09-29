-- Prove2me | Theorems.Thm_Ihara_ker_pow_eq_one_of_stem
-- name    : Ihara.ker_pow_eq_one_of_stem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/051985e4-2d37-5c72-9f42-7613b0f00155
-- title:
--   Odd exponent descends to the kernel of a stem extension
-- statement:
--   Let $E$ and $G$ be groups in a common universe and let $\pi : E \to G$ be a group homomorphism which is surjective and whose kernel is contained both in the centre of $E$ and in the commutator subgroup of $E$. Let $K$ be a normal subgroup of $G$ with $K$ contained in the commutator subgroup of $G$, and suppose $K$ is abelian, in the sense that any two of its elements commute. Suppose further that the quotient $G/K$ has trivial Schur multiplier in the stem-extension sense of [`Ihara.HasTrivialSchurMultiplier`](def/SchurMultiplierTrivial.html#L11): for every group $E'$ in the same universe and every surjective homomorphism $\pi' : E' \to G/K$ whose kernel lies in the centre of $E'$ and in the commutator subgroup of $E'$, that kernel is trivial. Finally let $q$ be an odd natural number such that $k^q = 1$ for every $k \in K$. The conclusion is that $c^q = 1$ for every $c$ in the kernel of $\pi$.
--
--   This is the exponent step in the stem-extension descent used to compute Schur multipliers of the groups $\mathrm{SL}_2(\mathbb{Z}/m)$: an odd exponent bound on an abelian normal layer $K \le [G,G]$, together with stem-triviality of $G/K$, propagates to the kernel of any stem extension of $G$. It is cited in the proof of [`Ihara.hasTrivialSchurMultiplier_SL2_ZMod_sq`](thm.html#Ihara.hasTrivialSchurMultiplier_SL2_ZMod_sq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_ker_pow_eq_one_of_stem.lean

import Definitions.Def_SchurMultiplierTrivial
import Mathlib.Algebra.Group.Nat.Even

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem Ihara.ker_pow_eq_one_of_stem {E G : Type u} [Group E] [Group G] (π : E →* G)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hcomm : π.ker ≤ commutator E) (K : Subgroup G) [K.Normal] (hK : K ≤ commutator G)
    (hQ : Ihara.HasTrivialSchurMultiplier (G ⧸ K)) (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    {q : ℕ} (hq : Odd q) (hKq : ∀ k ∈ K, k ^ q = 1) : ∀ c ∈ π.ker, c ^ q = 1 := by sorry
