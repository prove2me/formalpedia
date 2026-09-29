-- Prove2me | Theorems.Thm_ModularCurve_heckeAlphaCIntegral_unconditional
-- name    : ModularCurve.heckeAlphaCIntegral_unconditional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/ea521f3b-edb6-5636-99b2-cc079460739c
-- title:
--   Unconditional integrality of the degeneracy leg `heckeAlphaC`
-- statement:
--   Let $k$ be an arbitrary field and let $N$ and $q$ be natural numbers, both nonzero. The assertion is the predicate `HeckeAlphaCIntegral k N q`, which by definition says that the ring homomorphism underlying the $k$-algebra map `heckeAlphaC k N q` is integral. That algebra map is nothing but the inclusion of intermediate fields provided by `modularFunctionFieldC_le_charLDegeneracyRoof k N q`, namely the inclusion of the level-$N$ modular function field `modularFunctionFieldC k N` over $k$ into the intermediate field `charLDegeneracyRoof k N q`. Unwound, the conclusion is therefore: every element of `charLDegeneracyRoof k N q` is a root of a monic polynomial whose coefficients lie in (the image of) `modularFunctionFieldC k N`. The word "unconditional" records the absence of further hypotheses: no condition is imposed on the characteristic of $k$, $k$ is not assumed algebraically closed, and no coprimality or other relation between $N$ and $q$ is required — only that both are nonzero.
--
--   This is the integrality of the forgetful leg of the degeneracy correspondence relating level $N$ to level $Nq$, in the function-field formulation used throughout the characteristic-$\ell$ part of the argument; classically it is the statement that the $q$-th modular equation makes the $j$-invariants of the $q$-isogenous level structures integral over the level-$N$ modular function field. It is used as a standing input by the later results on Hecke transport, specialisation of places and level structures at $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeAlphaCIntegral_unconditional.lean

import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.heckeAlphaCIntegral_unconditional (k : Type*) [Field k] (N q : ℕ) [NeZero N] [NeZero q] :
    HeckeAlphaCIntegral k N q := by sorry
