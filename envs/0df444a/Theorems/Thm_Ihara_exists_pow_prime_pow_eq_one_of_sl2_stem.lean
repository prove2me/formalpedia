-- Prove2me | Theorems.Thm_Ihara_exists_pow_prime_pow_eq_one_of_sl2_stem
-- name    : Ihara.exists_pow_prime_pow_eq_one_of_sl2_stem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/009db2cd-bfb0-5166-8c13-2737a1081404
-- title:
--   Central extensions of SL₂(ℤ/q): commutator kernel is q-torsion
-- statement:
--   Let $q$ be a prime with $q \neq 2$, and let $E$ be a group in the lowest universe equipped with a group homomorphism $\pi : E \to \mathrm{SL}_2(\mathbb{Z}/q)$ (the special linear group of $2 \times 2$ matrices indexed by `Fin 2` over `ZMod q`). Assume that $\pi$ is surjective as a function and that its kernel is contained in the centre of $E$, so that $\pi$ exhibits $E$ as a central extension of $\mathrm{SL}_2(\mathbb{Z}/q)$. Let $x$ be an element of $E$ lying both in the kernel of $\pi$ and in the commutator subgroup $[E,E]$ of $E$. The conclusion is that there exists a natural number $k$ with $x^{q^k} = 1$; that is, every element of $\ker \pi \cap [E,E]$ has order a power of $q$ (the case $k = 0$ being allowed, and no bound on $k$ being asserted).
--
--   This is the prime-to-$q$ half of the computation of the Schur multiplier of $\mathrm{SL}_2(\mathbb{Z}/q)$ for odd $q$: in a stem-type central extension the obstruction group $\ker\pi \cap [E,E]$ can only contain $q$-torsion, the $\ell$-part for each $\ell \neq q$ being removed by transfer to a cyclic or dicyclic subgroup of $\ell$-free index (the dicyclic case entering through [`Ihara.ker_inf_commutator_eq_bot_of_dicyclic_closure_pair`](thm.html#Ihara.ker_inf_commutator_eq_bot_of_dicyclic_closure_pair)). It feeds the statements that $\mathrm{SL}_2(\mathbb{Z}/q)$ and $\mathrm{SL}_2(\mathbb{Z}/q^n)$ have trivial Schur multiplier for odd primes $q$, which are used in the group-theoretic input to Ihara's lemma.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_exists_pow_prime_pow_eq_one_of_sl2_stem.lean

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Center

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups in

theorem Ihara.exists_pow_prime_pow_eq_one_of_sl2_stem (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    {E : Type} [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q))
    (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) {x : E} (hx : x ∈ π.ker)
    (hxcomm : x ∈ commutator E) :
    ∃ k : ℕ, x ^ q ^ k = 1 := by sorry
