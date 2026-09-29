-- Prove2me | Theorems.Thm_IsAdicComplete_of_finite_of_isNoetherianRing
-- name    : IsAdicComplete.of_finite_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/080b1f95-16f3-54c6-b553-2e9ab8cb96ae
-- title:
--   Finite modules over a complete Noetherian ring are complete
-- statement:
--   Let $R$ be a commutative Noetherian ring, let $I \subseteq R$ be an ideal, and assume that $R$ is $I$-adically complete in Mathlib's sense (`IsAdicComplete I R`, i.e. the $I$-adic filtration on $R$ is Hausdorff and every Cauchy-type sequence for it has a limit, equivalently the canonical map $R \to \varprojlim_n R/I^n$ is bijective). Let $M$ be an $R$-module which is finitely generated over $R$. The conclusion is that $M$ is $I$-adically complete as well: `IsAdicComplete I M` holds, i.e. the $I$-adic filtration $(I^n \cdot M)_n$ on $M$ is separated and complete, equivalently the canonical map $M \to \varprojlim_n M/I^n M$ is bijective. No hypothesis of finite presentation or of $I$ being finitely generated beyond Noetherianity is needed, and no restriction is placed on the universe of $M$ relative to that of $R$.
--
--   This is the standard fact that $I$-adic completeness passes from a Noetherian base ring to its finitely generated modules, underlying the identification $\hat R \otimes_R M \cong \hat M$. It is used in the project for adic-completion arguments, for instance in the description of completions as quotients of multivariate power series rings and in the existence and uniqueness statements for maps out of proper schemes over a complete base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsAdicComplete_of_finite_of_isNoetherianRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsAdicComplete.of_finite_of_isNoetherianRing
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by sorry
