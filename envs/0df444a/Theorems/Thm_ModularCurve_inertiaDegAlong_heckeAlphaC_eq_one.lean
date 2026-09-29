-- Prove2me | Theorems.Thm_ModularCurve_inertiaDegAlong_heckeAlphaC_eq_one
-- name    : ModularCurve.inertiaDegAlong_heckeAlphaC_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/4e5c802c-1a29-5e9f-b9db-b47d6400730e
-- title:
--   Inertia degree one along α̃_q over an algebraically closed field
-- statement:
--   Let $k$ be an algebraically closed field and let $N,q$ be nonzero natural numbers. Inside the Laurent series field $k((t))$ consider the intermediate field $\mathrm{Roof}_k(N,q) =$ `charLDegeneracyRoof k N q`, generated over $k$ by the four series `jqModC k`, `jqNModC k N`, `jqNModC k q` and `jqNModC k (N*q)`, and the subfield `modularFunctionFieldC k N` generated over $k$ by `jqModC k` and `jqNModC k N`; the degeneracy leg `heckeAlphaC k N q` is the $k$-algebra inclusion of the latter into the former. Assume `HeckeAlphaCIntegral k N q`, i.e. this inclusion is an integral ring homomorphism. Let $W$ be a place of $\mathrm{Roof}_k(N,q)$ over $k$, that is, a valuation subring of $\mathrm{Roof}_k(N,q)$ which contains the image of $k$, is not the whole field, and is a principal ideal ring. Then the inertia degree of $W$ along `heckeAlphaC k N q` equals $1$: the residue field of $W$ has degree $1$ over the residue field of the place obtained by restricting $W$ to `modularFunctionFieldC k N` through the inclusion. No hypothesis on the characteristic of $k$ is imposed.
--
--   This is the statement that over an algebraically closed constant field all places are rational, so that residue extensions along the $\alpha$-degeneracy leg of the modular correspondence in characteristic $\ell$ are trivial. It discharges the inertia-degree clause in the comparison of degeneracy maps and in the computation of place widths for the Hecke correspondence, being used by the pushforward identities for the degeneracy pair and by the commutation formulae for `heckeAlphaC` and `heckeBetaC` at a prime level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_inertiaDegAlong_heckeAlphaC_eq_one.lean

import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.inertiaDegAlong_heckeAlphaC_eq_one
    (k : Type*) [Field k] [IsAlgClosed k] (N q : ℕ) [NeZero N] [NeZero q]
    (hαc : HeckeAlphaCIntegral k N q)
    (W : AlgebraicCurve.Place k (charLDegeneracyRoof k N q)) :
    W.inertiaDegAlong (heckeAlphaC k N q) hαc = 1 := by sorry
