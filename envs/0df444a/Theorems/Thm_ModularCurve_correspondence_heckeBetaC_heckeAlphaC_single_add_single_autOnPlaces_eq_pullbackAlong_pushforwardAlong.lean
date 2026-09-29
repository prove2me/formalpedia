-- Prove2me | Theorems.Thm_ModularCurve_correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong
-- name    : ModularCurve.correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/1cf08b8d-d48d-5da5-99f1-592713d949dd
-- title:
--   Uₛ plus Atkin–Lehner equals b^*a_* on divisors
-- statement:
--   Let $M,s\ge 1$ with $s$ prime and $s\nmid M$, and let $k$ be a field of characteristic $p$ with $p\nmid Ms$. Inside $k((q))$ write $F_N=$ `modularFunctionFieldC k N` $=k\bigl(j(q),j(q^N)\bigr)$, and assume $j(q^M)\in F_{Ms}$ (hypothesis `hM`) and $j(q^s)\in F_{Ms}$ (hypothesis `hS`). Let $\sigma$ be a $k$-algebra automorphism of $F_{Ms}$ satisfying `IsAtkinLehnerLevelAut`, i.e. $\sigma$ interchanges $j(q)$ with $j(q^s)$ and interchanges $j(q^{Ms})$ with $j(q^M)$. Assume that divisors of nonzero functions exist and have degree $0$ both for the roof $R=k\bigl(j(q),j(q^{Ms}),j(q^s),j(q^{Ms^2})\bigr)=$ `charLDegeneracyRoof k (M*s) s` and for $F_{Ms}$, and assume integrality of the four maps involved: the inclusion $\alpha\colon F_{Ms}\hookrightarrow R$, the map $\beta\colon F_{Ms}\to R$ induced by $q\mapsto q^{s}$, the inclusion $a\colon F_M\hookrightarrow F_{Ms}$ and the map $b\colon F_M\to F_{Ms}$ induced by $q\mapsto q^{s}$. Then for every place $x$ of $F_{Ms}$ over $k$, the divisor obtained from $[x]$ by pulling back along $\beta$ and pushing forward along $\alpha$ (push-forward weighting a place of $R$ by its inertia degree), plus the single place $[\sigma x]$ obtained by transport of structure along $\sigma$, equals the pull-back along $b$ of the push-forward along $a$ of $[x]$.
--
--   This is the divisor-theoretic form of the classical identity $U_s+w_s=b^{*}a_{*}$ at level $Ms$ relating the Hecke correspondence at the prime $s$, the Atkin–Lehner involution $w_s$ and the two degeneracy maps $X_0(Ms)\rightrightarrows X_0(M)$. It feeds the verification of the Hecke and Atkin–Lehner laws on the combinatorial data attached to the supersingular special fibre, being cited by [`ModularCurve.SSLevelDatum.atkinLehnerPerm_swap_degeneracy_and_width_and_edgeHecke_adjoint`](thm.html#ModularCurve.SSLevelDatum.atkinLehnerPerm_swap_degeneracy_and_width_and_edgeHecke_adjoint), [`ModularCurve.SSLevelDatum.degeneracyMatrix_mulVec_padj_and_edgeHecke_companion_laws`](thm.html#ModularCurve.SSLevelDatum.degeneracyMatrix_mulVec_padj_and_edgeHecke_companion_laws) and [`ModularCurve.SSLevelDatum.heckeLaws_of_prime_ne_of_not_dvd`](thm.html#ModularCurve.SSLevelDatum.heckeLaws_of_prime_ne_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong.lean

import Mathlib
import Definitions.Def_ModularCurve_SSDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong
    (M s : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] (p : ℕ) [CharP k p] (hp : ¬ p ∣ M * s)
    (hM : jqNModC k M ∈ modularFunctionFieldC k (M * s)) (hS : jqNModC k s ∈ modularFunctionFieldC k (M * s))
    (σ : ↥(modularFunctionFieldC k (M * s)) ≃ₐ[k] ↥(modularFunctionFieldC k (M * s)))
    (hσ : IsAtkinLehnerLevelAut k M s hM hS σ) :
    ∀ [HasPrincipalDivisors k ↥(charLDegeneracyRoof k (M * s) s)]
      [HasPrincipalDivisors k ↥(modularFunctionFieldC k (M * s))]
      (hα : HeckeAlphaCIntegral k (M * s) s) (hβ : HeckeBetaCIntegral k (M * s) s)
      (ha : (levelAlphaC k M s hM).toRingHom.IsIntegral) (hb : (levelBetaC k M s hS).toRingHom.IsIntegral)
      (x : Place k ↥(modularFunctionFieldC k (M * s))),
      Divisor.correspondence (heckeBetaC k (M * s) s) (heckeAlphaC k (M * s) s) hβ hα (Finsupp.single x 1)
          + Finsupp.single (autOnPlaces k M s σ x) 1
        = Divisor.pullbackAlong (levelBetaC k M s hS) hb
            (Divisor.pushforwardAlong (levelAlphaC k M s hM) ha (Finsupp.single x 1)) := by sorry
