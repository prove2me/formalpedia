-- Prove2me | Theorems.Thm_ModularCurve_restrictAlong_heckeAlphaC_mem_ssPlaces_of_restrictAlong_heckeBetaC_mem_ssPlaces
-- name    : ModularCurve.restrictAlong_heckeAlphaC_mem_ssPlaces_of_restrictAlong_heckeBetaC_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/c7cc0cc0-04cf-5cce-8aa4-075f61ea3818
-- title:
--   Hecke correspondence at ℓ preserves supersingular places
-- statement:
--   Fix natural numbers $q'$, $N$, $\ell$ with $N \neq 0$, $q'$ prime, $\ell$ prime, $\ell \neq q'$ and $q' \nmid N$, and let $k$ be an algebraically closed field of characteristic $q'$. Inside the Laurent series field $k((q))$ consider the intermediate field $F_N$ given by `modularFunctionFieldC k N`, generated over $k$ by $j(q)$ and $j(q^N)$, and the roof $R$ given by `charLDegeneracyRoof k N ℓ`, generated over $k$ by $j(q)$, $j(q^N)$, $j(q^{\ell})$ and $j(q^{N\ell})$. Let $\alpha$, given by `heckeAlphaC k N ℓ`, be the inclusion $F_N \to R$ and $\beta$, given by `heckeBetaC k N ℓ`, the $k$-algebra map $F_N \to R$ induced by $q \mapsto q^{\ell}$, and assume hypotheses $h\alpha$, $h\beta$ that the underlying ring homomorphisms of $\alpha$ and $\beta$ are integral. Then for every place $W$ of $R$ over $k$ (a valuation subring of $R$ containing $k$, not all of $R$, whose valuation ring is a principal ideal ring), if the place of $F_N$ obtained by pulling $W$ back along $\beta$ lies in `ssPlaces q' N k` — that is, it is rational, satisfies `IsAffineGeomPlace`, and its value on `jGeomGen k N` lies in `ssJSet q' k` — then the pullback of $W$ along $\alpha$ lies in `ssPlaces q' N k` as well.
--
--   This is the statement, at the level of places of the function fields, that the Hecke (or degeneracy) correspondence at a prime $\ell$ different from the residue characteristic $q'$ carries the supersingular locus of $X_0(N)$ in characteristic $q'$ into itself, so that $\alpha_*\beta^*$ of a supersingular place is supported on supersingular places. It is used in the construction of the supersingular Hecke matrices, being cited by [`ModularCurve.SSLevelDatum.exists_heckeRowSums_and_adjointPair_laws`](thm.html#ModularCurve.SSLevelDatum.exists_heckeRowSums_and_adjointPair_laws) and [`ModularCurve.SSLevelDatum.heckeLaws_of_prime_ne_of_not_dvd`](thm.html#ModularCurve.SSLevelDatum.heckeLaws_of_prime_ne_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_restrictAlong_heckeAlphaC_mem_ssPlaces_of_restrictAlong_heckeBetaC_mem_ssPlaces.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_SupersingularNodePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.restrictAlong_heckeAlphaC_mem_ssPlaces_of_restrictAlong_heckeBetaC_mem_ssPlaces
    (q' N ℓ : ℕ) [NeZero N] [Fact q'.Prime] (hℓ : ℓ.Prime) (hℓq' : ℓ ≠ q') (hq'N : ¬ q' ∣ N)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k] :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∀ (hα : HeckeAlphaCIntegral k N ℓ) (hβ : HeckeBetaCIntegral k N ℓ)
      (W : Place k ↥(charLDegeneracyRoof k N ℓ)),
      W.restrictAlong (heckeBetaC k N ℓ) hβ ∈ ssPlaces q' N k →
        W.restrictAlong (heckeAlphaC k N ℓ) hα ∈ ssPlaces q' N k := by sorry
