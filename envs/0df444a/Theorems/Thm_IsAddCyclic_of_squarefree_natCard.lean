-- Prove2me | Theorems.Thm_IsAddCyclic_of_squarefree_natCard
-- name    : IsAddCyclic.of_squarefree_natCard
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/14855747-d0f6-58c2-8d76-6caa8c9e1383
-- title:
--   Abelian groups of squarefree order are cyclic
-- statement:
--   Let $A$ be an additive abelian group (no finiteness is assumed as a separate hypothesis) and suppose the natural number $\mathrm{Nat.card}\,A$ is squarefree, i.e. every element of $\mathbb{N}$ whose square divides it is a unit. Since a squarefree natural number is nonzero, this hypothesis already forces $A$ to be finite, with $\mathrm{Nat.card}\,A$ its order. The conclusion is `IsAddCyclic A`: the group $A$ is cyclic, that is, there is an element $g \in A$ such that every element of $A$ is an integer multiple of $g$. Note that the hypothesis is on the cardinality in the `Nat.card` sense, so for an infinite $A$ the value would be $0$, which is not squarefree; thus the statement is exactly the assertion that a finite abelian group whose order is squarefree is cyclic, phrased additively.
--
--   This is the classical fact that a finite abelian group of squarefree order is cyclic. In this development it supplies the cyclicity of subgroups of torsion groups of elliptic curves of squarefree order, and is used by [`WeierstrassCurve.Affine.IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq`](thm.html#WeierstrassCurve.Affine.IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsAddCyclic_of_squarefree_natCard.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsAddCyclic.of_squarefree_natCard
    {A : Type*} [AddCommGroup A] (hA : Squarefree (Nat.card A)) : IsAddCyclic A := by sorry
