-- Prove2me | Theorems.Thm_Ihara_hasTrivialSchurMultiplier_of_sylow
-- name    : Ihara.hasTrivialSchurMultiplier_of_sylow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/e61f8a5b-db2e-5e85-8976-e97531c8704e
-- title:
--   Schur's Sylow criterion for trivial Schur multiplier
-- statement:
--   Let $G$ be a finite group. Say that a group $H$ has the property [`Ihara.HasTrivialSchurMultiplier`](def/SchurMultiplierTrivial.html#L11) when for every group $E$ (in the same universe as $H$) and every surjective homomorphism $\pi : E \to H$ such that $\ker \pi$ is contained in the centre of $E$ and $\ker \pi$ is contained in the commutator subgroup $[E,E]$, one has $\ker \pi = 1$; that is, $H$ admits no nontrivial stem extension. The theorem asserts: if for every prime $p$ and every Sylow $p$-subgroup $P$ of $G$ the group $\uparrow P$ (the subgroup $P$ regarded as a group in its own right) satisfies [`Ihara.HasTrivialSchurMultiplier`](def/SchurMultiplierTrivial.html#L11), then $G$ satisfies [`Ihara.HasTrivialSchurMultiplier`](def/SchurMultiplierTrivial.html#L11). Unfolding the conclusion: for every group $E$ and every surjective $\pi : E \to G$ with $\ker \pi \le Z(E)$ and $\ker \pi \le [E,E]$, the kernel $\pi$ is trivial, so $\pi$ is an isomorphism.
--
--   This is Schur's classical result, in stem-extension form, that the $p$-primary part of the Schur multiplier of a finite group embeds into the Schur multiplier of a Sylow $p$-subgroup, so that vanishing for all Sylow subgroups forces vanishing for $G$. It is used to establish that $\mathrm{SL}_2(\mathbb{Z}/p)$ has trivial Schur multiplier for a prime $p$, in the form [`Ihara.hasTrivialSchurMultiplier_SL2_ZMod_of_prime`](thm.html#Ihara.hasTrivialSchurMultiplier_SL2_ZMod_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_hasTrivialSchurMultiplier_of_sylow.lean

import Mathlib.GroupTheory.Sylow
import Definitions.Def_SchurMultiplierTrivial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Ihara.hasTrivialSchurMultiplier_of_sylow
    {G : Type*} [Group G] [Finite G]
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      Ihara.HasTrivialSchurMultiplier ↥(P : Subgroup G)) :
    Ihara.HasTrivialSchurMultiplier G := by sorry
