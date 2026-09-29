-- Prove2me | Theorems.Thm_Ihara_card_ker_dvd_two_of_stemExtension_SL2_ZMod_two_pow
-- name    : Ihara.card_ker_dvd_two_of_stemExtension_SL2_ZMod_two_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/6da6692f-0971-57d4-8589-d5844fe8f7fa
-- title:
--   Stem extensions of SL(2,ℤ/2ᵃ) have kernel of order dividing 2
-- statement:
--   Let $a$ be a natural number and let $E$ be a group (in the type-theoretic sense, a type `E` carrying a group structure) equipped with a monoid homomorphism $\pi : E \to SL(2, \mathbb{Z}/2^a\mathbb{Z})$, where $SL(2,\mathbb{Z}/2^a\mathbb{Z})$ denotes the special linear group of $2\times 2$ matrices over the ring $\mathbb{Z}/2^a\mathbb{Z}$ in the `MatrixGroups` notation. Assume three hypotheses: $\pi$ is surjective as a function; the kernel of $\pi$ is contained in the centre of $E$ as a subgroup; and the kernel of $\pi$ is contained in the commutator subgroup of $E$. Thus $E$ is a central extension of $SL(2,\mathbb{Z}/2^a\mathbb{Z})$ whose kernel lies in $[E,E]$, i.e. a stem extension. The conclusion is that the natural-number cardinality of the kernel of $\pi$, as given by `Nat.card` (so the value $0$ in the case of an infinite kernel), divides $2$. In particular the kernel is finite, of order $1$ or $2$; no claim is made as to which of the two occurs for a given $a$.
--
--   This is the bound on stem extensions of $SL(2,\mathbb{Z}/2^a\mathbb{Z})$ corresponding to the fact that the Schur multiplier of this group has order at most $2$ (and is exactly $\mathbb{Z}/2$ for $a \ge 2$, by Beyl's computation). It is used in the proof of [`Ihara.mennickeCSP_of_prime`](thm.html#Ihara.mennickeCSP_of_prime), in the line of argument on the congruence subgroup property for Ihara's modular group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_card_ker_dvd_two_of_stemExtension_SL2_ZMod_two_pow.lean

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Commutator.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem Ihara.card_ker_dvd_two_of_stemExtension_SL2_ZMod_two_pow {a : ℕ} (E : Type) [Group E]
    (π : E →* SL(2, ZMod (2 ^ a))) (hπ : Function.Surjective π)
    (hcen : MonoidHom.ker π ≤ Subgroup.center E) (hcomm : MonoidHom.ker π ≤ commutator E) :
    Nat.card (MonoidHom.ker π) ∣ 2 := by sorry
