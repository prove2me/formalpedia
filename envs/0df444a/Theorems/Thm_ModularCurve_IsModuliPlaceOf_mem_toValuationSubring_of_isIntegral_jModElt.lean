-- Prove2me | Theorems.Thm_ModularCurve_IsModuliPlaceOf_mem_toValuationSubring_of_isIntegral_jModElt
-- name    : ModularCurve.IsModuliPlaceOf.mem_toValuationSubring_of_isIntegral_jModElt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/9c0c018a-b415-5819-b3cf-d3aaa3d01c23
-- title:
--   Moduli places contain everything integral over K[̃ j]
-- statement:
--   Let $K$ be a field and $N$ a nonzero natural number, and write $F_N =$ [`ModularCurve.modularFunctionFieldFullC K N`](def/ModularCurve_X0ModL.html#L100) for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the series $q^{*}$-expansions `qExpand K d (jqModC K)` for the divisors $d \mid N$, $d \neq 0$. Let $x$ be a moduli point of level $N$ over $K$, i.e. a class of pairs (Weierstrass curve over $K$ with invertible discriminant, point of additive order exactly $N$) modulo variable changes composed with multiplication by integers coprime to $N$, and let $v$ be a place of $F_N$ over $K$: a valuation subring of $F_N$ containing the image of $K$, different from all of $F_N$, and a principal ideal ring. Assume [`ModularCurve.IsModuliPlaceOf K N x v`](def/ModularCurve_ModuliPlace.html#L325), that is, there are a field $\Omega$ over $K$ and a moduli test datum for $x$ over $\Omega$ (a place $W$ of $\Omega$ over $K$, a Weierstrass curve over the valuation ring of $W$ whose reduction has nonzero discriminant, a point of order $N$ on it reducing to $x$ via a retraction of the residue field onto $K$, and a $K$-embedding $\mathrm{emb} : F_N \to \Omega$ matching the functions `jqNFull K N d hd` with the cyclic-quotient $j$-invariants of the curve) such that the valuation subring of $v$ is the preimage under $\mathrm{emb}$ of that of $W$. Let $a \in F_N$ and suppose there is a monic polynomial $P$ with coefficients in $K[X]$ which, after applying to its coefficients the $K$-algebra map $K[X] \to F_N$ sending $X$ to $\tilde j =$ [`ModularCurve.jModElt`](def/ModularCurve_QAdicPlaceMod.html#L80) (the element of $F_N$ given by the series `jqModC K`), vanishes at $a$; that is, $a$ is integral over the subring $K[\tilde j]$ of $F_N$. Then $a$ lies in the valuation subring of $v$.
--
--   This is the statement that the valuation ring of a moduli place of $x$ contains the integral closure of $K[\tilde j]$ in $F_N$; it supplies the hypothesis needed to identify such a place, and is used in the proof that a moduli place of $x$ is uniquely determined by $x$ ([`ModularCurve.eq_of_isModuliPlaceOf`](thm.html#ModularCurve.eq_of_isModuliPlaceOf)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsModuliPlaceOf_mem_toValuationSubring_of_isIntegral_jModElt.lean

import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.IsModuliPlaceOf.mem_toValuationSubring_of_isIntegral_jModElt
    (K : Type u) [Field K] [DecidableEq K] (N : ℕ) [NeZero N]
    (x : ModularCurve.ModuliPoint N K) (v : AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldFullC K N))
    (h : ModularCurve.IsModuliPlaceOf K N x v)
    (a : ↥(ModularCurve.modularFunctionFieldFullC K N)) (ha : (∃ P : Polynomial (Polynomial K), P.Monic ∧ Polynomial.eval₂ (Polynomial.aeval (R := K) (ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N))).toRingHom a P = 0)) :
    a ∈ v.toValuationSubring := by sorry
