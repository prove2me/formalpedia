-- Prove2me | Theorems.Thm_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq
-- name    : Ihara.hasTrivialSchurMultiplier_SL2_ZMod_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/dbc63730-ed08-5eec-a51b-308922c90e71
-- title:
--   Trivial Schur multiplier for SL₂(ℤ/q²)
-- statement:
--   Let $q$ be a prime with $q \ge 5$. Assume that $\mathrm{SL}_2(\mathbb{Z}/q^2\mathbb{Z})$ is perfect, in the sense that its commutator subgroup is the whole group, and assume that $\mathrm{SL}_2(\mathbb{Z}/q^1\mathbb{Z})$ has trivial Schur multiplier in the stem-extension sense used throughout, namely: for every group $E$ and every surjective homomorphism $\pi : E \to \mathrm{SL}_2(\mathbb{Z}/q\mathbb{Z})$ whose kernel is contained both in the centre of $E$ and in the commutator subgroup of $E$, one has $\ker \pi = 1$. The conclusion is the same property for $\mathrm{SL}_2(\mathbb{Z}/q^2\mathbb{Z})$: for every group $E$ (in the same universe) and every surjective homomorphism $\pi : E \to \mathrm{SL}_2(\mathbb{Z}/q^2\mathbb{Z})$ with $\ker \pi \le Z(E)$ and $\ker \pi \le [E,E]$, the kernel of $\pi$ is trivial. Here the modulus in the hypothesis is written as the first power $q^1$, matching the exponent bookkeeping of the induction on $m$ in $\mathrm{SL}_2(\mathbb{Z}/q^m\mathbb{Z})$; no further structure on $E$ beyond being a group is assumed.
--
--   This is the base case $m = 2$ of the induction, due to Mennicke, showing that $\mathrm{SL}_2(\mathbb{Z}/q^m\mathbb{Z})$ admits no non-trivial stem extension for $q \ge 5$ prime, equivalently that its Schur multiplier vanishes. It is cited by [`Ihara.hasTrivialSchurMultiplier_SL2_ZMod_prime_pow`](thm.html#Ihara.hasTrivialSchurMultiplier_SL2_ZMod_prime_pow), which runs the induction over all prime powers; the proof combines the abstract fibre criterion [`Ihara.ker_eq_bot_of_stem_of_fibre`](thm.html#Ihara.ker_eq_bot_of_stem_of_fibre), the commutation of preimages of the level-$q$ congruence subgroup [`Ihara.sl2_zmod_sq_congruence_preimage_commute`](thm.html#Ihara.sl2_zmod_sq_congruence_preimage_commute), and the exponent bound [`Ihara.ker_pow_eq_one_of_stem`](thm.html#Ihara.ker_pow_eq_one_of_stem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.lean

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Definitions.Def_SchurMultiplierTrivial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem Ihara.hasTrivialSchurMultiplier_SL2_ZMod_sq (q : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q)
    (hperf : commutator SL(2, ZMod (q ^ 2)) = ⊤)
    (IH : Ihara.HasTrivialSchurMultiplier SL(2, ZMod (q ^ 1))) :
    Ihara.HasTrivialSchurMultiplier SL(2, ZMod (q ^ 2)) := by sorry
