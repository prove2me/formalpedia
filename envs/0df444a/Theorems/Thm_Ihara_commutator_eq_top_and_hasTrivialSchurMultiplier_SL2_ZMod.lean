-- Prove2me | Theorems.Thm_Ihara_commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod
-- name    : Ihara.commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/539bf5af-34bf-5b9c-ae5c-8a673602ec3e
-- title:
--   Perfectness and trivial Schur multiplier of SL₂(ℤ/m)
-- statement:
--   Two hypotheses on prime powers are assumed: `hP1`, that for every prime $p \ge 5$ and every $n \neq 0$ the commutator subgroup of $\mathrm{SL}_2(\mathbb{Z}/p^n)$ is the whole group; and `hP2`, that for the same $p$ and $n$ the group $\mathrm{SL}_2(\mathbb{Z}/p^n)$ satisfies [`Ihara.HasTrivialSchurMultiplier`](def/SchurMultiplierTrivial.html#L11), i.e. every group $E$ together with a surjective homomorphism $\pi : E \to \mathrm{SL}_2(\mathbb{Z}/p^n)$ whose kernel lies both in the centre of $E$ and in the commutator subgroup of $E$ has $\ker \pi$ trivial. Let $m$ be a natural number such that every prime $p$ dividing $m$ satisfies $5 \le p$ (in particular $m \neq 0$, since $2 \mid 0$, while $m = 1$ is allowed). The conclusion is the conjunction of the same two properties for $m$: the commutator subgroup of $\mathrm{SL}_2(\mathbb{Z}/m)$ is all of $\mathrm{SL}_2(\mathbb{Z}/m)$, and for every group $E$ and every surjective homomorphism $\pi : E \to \mathrm{SL}_2(\mathbb{Z}/m)$ with $\ker \pi$ contained in the centre of $E$ and in the commutator subgroup of $E$, the kernel $\ker \pi$ is trivial. Here $\mathrm{SL}(2,\cdot)$ is written with the `MatrixGroups` notation.
--
--   This is the passage from prime powers to general moduli with all prime factors at least $5$ for the two standard facts that $\mathrm{SL}_2(\mathbb{Z}/m)$ is perfect and has trivial Schur multiplier (in the form: no non-split central extension by a subgroup of the commutator subgroup). It feeds the treatment of Ihara's modular group and the congruence subgroup property, being used by [`Ihara.gamma0Away_hom_factor`](thm.html#Ihara.gamma0Away_hom_factor) and [`Ihara.mennickeCSP_of_prime`](thm.html#Ihara.mennickeCSP_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod.lean

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Definitions.Def_SchurMultiplierTrivial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem Ihara.commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod
    (hP1 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → commutator (SL(2, ZMod (p ^ n))) = ⊤)
    (hP2 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 →
      Ihara.HasTrivialSchurMultiplier (SL(2, ZMod (p ^ n))))
    (m : ℕ) (hm : ∀ p : ℕ, p.Prime → p ∣ m → 5 ≤ p) :
    commutator (SL(2, ZMod m)) = ⊤ ∧ Ihara.HasTrivialSchurMultiplier (SL(2, ZMod m)) := by sorry
