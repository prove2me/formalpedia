-- Prove2me | Theorems.Thm_ModularCurve_finiteAlong_heckeBetaC
-- name    : ModularCurve.finiteAlong_heckeBetaC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/765c2d15-9dd4-5265-973f-a829641d6f8f
-- title:
--   Finiteness of the q-twisting degeneracy embedding
-- statement:
--   Let $k$ be a field and let $N,q$ be natural numbers, both nonzero, with $q$ prime. Consider inside the field of Laurent series over $k$ the level-$N$ modular function field `modularFunctionFieldC k N`, namely the intermediate field obtained by adjoining to $k$ the two series $\mathrm{jqModC}\,k$ and $\mathrm{jqNModC}\,k\,N$, and the roof field `charLDegeneracyRoof k N q`, obtained by adjoining to $k$ the four series $\mathrm{jqModC}\,k$, $\mathrm{jqNModC}\,k\,N$, $\mathrm{jqNModC}\,k\,q$ and $\mathrm{jqNModC}\,k\,(Nq)$. The $k$-algebra map [`ModularCurve.heckeBetaC k N q`](def/ModularCurve_CharLDegeneracyHecke.html#L266) from the former to the latter is induced by `qExpand k q`, the ring endomorphism of Laurent series that multiplies all exponents by $q$ (substitution of the $q$-th power of the formal variable), which is known to carry the level-$N$ field into the roof field. The theorem asserts [`AlgebraicCurve.FiniteAlong`](def/AlgebraicCurve_Correspondence.html#L37) for this map: with the roof field regarded as an algebra over `modularFunctionFieldC k N` through `heckeBetaC k N q`, it is a finite module, i.e. the twisting degeneracy embedding is a module-finite extension.
--
--   This is the finiteness half of the degeneracy (twisting) map $\beta$ on modular function fields, the companion of the inclusion-type map $\alpha$; it rests on the symmetry of the modular equation $\Phi_q(X,Y)=\Phi_q(Y,X)$, which makes the generators of the level-$N$ field integral over the roof field's $q$-twisted generators. Finiteness is what allows norm and pushforward constructions on divisors and degree-zero Picard groups along $\beta$, and it is used in the verification of the commutation and adjointness laws for the resulting Hecke correspondences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteAlong_heckeBetaC.lean

import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.finiteAlong_heckeBetaC (k : Type*) [Field k] (N q : ℕ)
    [NeZero N] [NeZero q] [Fact q.Prime] :
    AlgebraicCurve.FiniteAlong k (ModularCurve.heckeBetaC k N q) := by sorry
