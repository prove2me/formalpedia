-- Prove2me | Theorems.Thm_ModularCurve_restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces_of_dvd
-- name    : ModularCurve.restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/4ad492b3-403d-5584-be36-7e88009d3d65
-- title:
--   Supersingularity along both legs of the ℓ-roof when ℓ ∣ N
-- statement:
--   Let $p$ be a prime and $K$ an algebraically closed field of characteristic $p$, let $N \ge 1$ and let $\ell$ be a prime with $(N : K) \ne 0$ (that is, $p \nmid N$), $\ell \mid N$ and $\ell \ne p$. Inside $\mathrm{LaurentSeries}\,K$ consider the level-$N$ modular function field $F = K(j(q), j(q^N))$, generated over $K$ by `jqModC K` and `jqNModC K N`, and the $\ell$-th degeneracy roof $R =$ `charLDegeneracyRoof K N ℓ` $= K(j(q), j(q^N), j(q^{\ell}), j(q^{N\ell}))$. Two $K$-algebra maps $F \to R$ are in play: `heckeAlphaC K N ℓ`, the inclusion, and `heckeBetaC K N ℓ`, induced by the substitution $q \mapsto q^{\ell}$ on Laurent series; both are assumed integral as ring homomorphisms, by hypotheses $h\alpha$ and $h\beta$. Given a place $y$ of $R$ over $K$, let $y|_{\alpha}$ and $y|_{\beta}$ denote its restrictions along these maps, the places of $F$ whose valuation subrings are the preimages of that of $y$. The assertion is that $y|_{\alpha}$ lies in `ssPlaces p N K` if and only if $y|_{\beta}$ does, where membership means: the place is rational, it is an affine geometric place for level $N$, and its value on the generator `jGeomGen K N` lies in the set `ssJSet p K` of supersingular $j$-invariants in characteristic $p$.
--
--   This is the statement that the two degeneracy maps $X_0(N\ell) \rightrightarrows X_0(N)$ in characteristic $p$ both preserve and reflect supersingularity of points, in the case where the prime $\ell$ already divides the level $N$; geometrically, the two restrictions of a place of the roof are centred at elliptic curves joined by a cyclic $\ell$-isogeny, and an isogeny of degree prime to $p$ does not change supersingularity. It feeds the computation of the Hecke correspondence on divisors supported at supersingular places, [`ModularCurve.exists_sum_ssPlaces_correspondence_heckeAlphaC_heckeBetaC_single_eq_of_dvd`](thm.html#ModularCurve.exists_sum_ssPlaces_correspondence_heckeAlphaC_heckeBetaC_single_eq_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces_of_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_PlaceWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve

theorem ModularCurve.restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces_of_dvd
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hN : (N : K) ≠ 0) (hℓN : ℓ ∣ N) (hℓp : ℓ ≠ p)
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (y : Place K ↥(charLDegeneracyRoof K N ℓ)) :
    y.restrictAlong (heckeAlphaC K N ℓ) hα ∈ ssPlaces p N K ↔ y.restrictAlong (heckeBetaC K N ℓ) hβ ∈ ssPlaces p N K := by sorry
