-- Prove2me | Theorems.Thm_ModularCurve_ord_heckeBetaC_jGeomGen_sub_algebraMap_eq_one
-- name    : ModularCurve.ord_heckeBetaC_jGeomGen_sub_algebraMap_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/f0e63821-ac44-5dbd-9caa-c2652df8ee41
-- title:
--   j(q^ℓ) - a' is a uniformiser at generic places of the roof
-- statement:
--   Let $q'$ be a prime and $k$ an algebraically closed field of characteristic $q'$. Let $N$ and $\ell$ be nonzero natural numbers with $\ell$ prime, $\ell \nmid N$, $q' \nmid N$ and $\ell \neq q'$. Write $R =$ `charLDegeneracyRoof k N ℓ` for the intermediate field of $k((q))$ generated over $k$ by the four series $\bar\jmath(q)$, $\bar\jmath(q^{N})$, $\bar\jmath(q^{\ell})$ and $\bar\jmath(q^{N\ell})$, where $\bar\jmath(q)$ is `jqModC k`, the reduction to $k$ of the $q$-expansion of the modular invariant, and $\bar\jmath(q^{d})$ is its image under the substitution $q \mapsto q^{d}$. Let $y$ be a place of $R$ over $k$, that is, a valuation subring of $R$ containing $k$, distinct from $R$ itself, and a principal ideal ring. Let $\beta =$ `heckeBetaC k N ℓ` be the $k$-algebra embedding of the level-$N$ modular function field $k(\bar\jmath(q), \bar\jmath(q^{N}))$ into $R$ given by $q \mapsto q^{\ell}$, and let $x = \beta(\bar\jmath(q)) = \bar\jmath(q^{\ell})$. Assume $x$ lies in the valuation subring of $y$, that its value $y$-evaluation $a' \in k$ (the residue of $x$ transported back along $k \to$ the residue field) satisfies $a' \neq 0$ and $a' \neq 1728$. Then the order of $x - a'$ at $y$, defined as minus the logarithm of the adic valuation attached to $y$, equals $1$.
--
--   This is the statement that the $\ell$-degeneracy map $\tau \mapsto \ell\tau$ from level $N\ell$ to level $N$ is unramified above the non-elliptic, non-cuspidal points in characteristic prime to $N\ell$: at a place of the level-$N\ell$ roof where $\bar\jmath(q^{\ell})$ takes a value other than $0$ and $1728$, the function $\bar\jmath(q^{\ell}) - a'$ is a uniformiser. It feeds the computation [`ModularCurve.ord_heckeMultiplier_eq_zero_of_evalAt_ne`](thm.html#ModularCurve.ord_heckeMultiplier_eq_zero_of_evalAt_ne) in the analysis of the Hecke correspondence on the special fibre in characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_heckeBetaC_jGeomGen_sub_algebraMap_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.ord_heckeBetaC_jGeomGen_sub_algebraMap_eq_one
    (q' : ℕ) [Fact q'.Prime] (k : Type*) [Field k] [CharP k q'] [IsAlgClosed k]
    (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hq'N : ¬ q' ∣ N) (hq'ℓ : ℓ ≠ q')
    (y : Place k ↥(charLDegeneracyRoof k N ℓ))
    (hy : heckeBetaC k N ℓ (jGeomGen k N) ∈ y.toValuationSubring)
    (a' : k) (ha' : y.evalAt (heckeBetaC k N ℓ (jGeomGen k N)) = a') (h0 : a' ≠ 0) (h1728 : a' ≠ 1728) :
    y.ord (heckeBetaC k N ℓ (jGeomGen k N) - algebraMap k ↥(charLDegeneracyRoof k N ℓ) a') = 1 := by sorry
