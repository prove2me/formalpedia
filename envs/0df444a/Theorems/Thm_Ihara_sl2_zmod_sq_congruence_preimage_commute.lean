-- Prove2me | Theorems.Thm_Ihara_sl2_zmod_sq_congruence_preimage_commute
-- name    : Ihara.sl2_zmod_sq_congruence_preimage_commute
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/8eec8f53-df44-576b-87c5-84dd9485d30f
-- title:
--   Congruence-kernel preimage in a central extension of SL₂(ℤ/q²) is abelian
-- statement:
--   Let $q$ be a natural number, let $E$ be a group, and let $\pi : E \to \mathrm{SL}_2(\mathbb{Z}/q^2\mathbb{Z})$ be a group homomorphism which is surjective and whose kernel is contained in the centre of $E$. Assume further that $q$ is prime and $q \ge 5$. Then for all $x, y \in E$ such that the matrix underlying $\pi(x)$ can be written as $1 + q \cdot A$ for some $2 \times 2$ matrix $A$ over $\mathbb{Z}/q^2\mathbb{Z}$ (the scalar action being multiplication by the image of $q$ in $\mathbb{Z}/q^2\mathbb{Z}$), and likewise the matrix underlying $\pi(y)$ equals $1 + q \cdot B$ for some $2 \times 2$ matrix $B$ over $\mathbb{Z}/q^2\mathbb{Z}$, the elements $x$ and $y$ commute in $E$, i.e. $xy = yx$. The two existential hypotheses are the explicit matrix form of the conditions $\pi(x) \equiv 1$ and $\pi(y) \equiv 1$ modulo $q$; thus the assertion is that the full preimage under $\pi$ of the level-$q$ congruence kernel of $\mathrm{SL}_2(\mathbb{Z}/q^2\mathbb{Z})$ is an abelian subgroup of $E$, stated here elementwise rather than as a statement about a subgroup.
--
--   This is the step, going back to Mennicke's analysis of Ihara's modular group, that in any central extension of $\mathrm{SL}_2(\mathbb{Z}/q^2\mathbb{Z})$ the preimage of the congruence kernel of level $q$ is abelian. It is used to prove that $\mathrm{SL}_2(\mathbb{Z}/q^2\mathbb{Z})$ has trivial Schur multiplier for primes $q \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_sl2_zmod_sq_congruence_preimage_commute.lean

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem Ihara.sl2_zmod_sq_congruence_preimage_commute (q : ℕ)
    {E : Type} [Group E] (π : E →* SL(2, ZMod (q ^ 2)))
    (hsurj : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hq : q.Prime) (hq5 : 5 ≤ q) :
    ∀ x, (∃ A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2)),
        ((π x : SL(2, ZMod (q ^ 2))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2)))
          = 1 + (q : ZMod (q ^ 2)) • A) →
    ∀ y, (∃ B : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2)),
        ((π y : SL(2, ZMod (q ^ 2))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2)))
          = 1 + (q : ZMod (q ^ 2)) • B) →
    Commute x y := by sorry
