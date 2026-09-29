-- Prove2me | Theorems.Thm_Ihara_mennickeCSP_of_coprime_of_stem
-- name    : Ihara.mennickeCSP_of_coprime_of_stem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/185f4dc4-2564-5648-87e2-8b39d5b7bce5
-- title:
--   Mennicke's congruence-subgroup property at a coprime level
-- statement:
--   Let $q$ be a nonzero natural number and $m$ a natural number with $\gcd(m,q)=1$ and also $\gcd(m,q^2-1)=1$ (natural subtraction). Write $R=\mathbb{Z}[1/q]$ for the localisation of $\mathbb{Z}$ away from $q$, let $A=\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)\in \mathrm{SL}_2(\mathbb{Z})$ and let $A_R$ be its image in $\mathrm{SL}_2(R)$ under the map induced by $\mathbb{Z}\to R$. Let $\rho_m\colon \mathrm{SL}_2(R)\to \mathrm{SL}_2(\mathbb{Z}/m)$ be induced by the ring homomorphism $R\to\mathbb{Z}/m$ obtained by lifting $\mathbb{Z}\to\mathbb{Z}/m$ (legitimate since $q$ is a unit modulo $m$), and let $N_m=\ker\rho_m$, $Q_m=\langle\!\langle A_R^{\,m}\rangle\!\rangle$ the normal closure of $A_R^{\,m}$ in $\mathrm{SL}_2(R)$. Assume: $N_m$ is contained in the join $[\mathrm{SL}_2(R),\mathrm{SL}_2(R)]\sqcup Q_m$ of subgroups; $\rho_m$ is surjective; and $\mathrm{SL}_2(\mathbb{Z}/m)$ has trivial Schur multiplier in the sense that for every group $E$ and every surjective homomorphism $\pi\colon E\to \mathrm{SL}_2(\mathbb{Z}/m)$ whose kernel lies both in the centre of $E$ and in the commutator subgroup of $E$, the kernel is trivial. Then $N_m=Q_m$.
--
--   This is Mennicke's congruence-subgroup statement for $\mathrm{SL}_2(\mathbb{Z}[1/q])$ at a level $m$ coprime to $q$, in the form: the principal congruence subgroup of level $m$ coincides with the normal closure of the $m$-th power of the elementary matrix $A$, granted the abelianised containment, surjectivity of reduction, and vanishing of the Schur multiplier of $\mathrm{SL}_2(\mathbb{Z}/m)$. It is used to obtain the congruence-subgroup property at prime levels and, through that, the factorisation of homomorphisms out of the Ihara group $\mathrm{SL}_2(\mathbb{Z}[1/q])$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_mennickeCSP_of_coprime_of_stem.lean

import Definitions.Def_IharaMennickeCarrier
import Definitions.Def_SchurMultiplierTrivial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem Ihara.mennickeCSP_of_coprime_of_stem (q m : ℕ) [NeZero q] (hmq : Nat.Coprime m q)
    (hcop : Nat.Coprime m (q ^ 2 - 1))
    (hhabel : Ihara.principalCongruenceAway m q hmq
      ≤ commutator (SL(2, Ihara.ZAway q)) ⊔ Ihara.mennickeQ q m)
    (hsurj : Function.Surjective (Ihara.slAwayReduction m q hmq))
    (hstem : Ihara.HasTrivialSchurMultiplier (SL(2, ZMod m))) :
    Ihara.MennickeCSP m q hmq := by sorry
