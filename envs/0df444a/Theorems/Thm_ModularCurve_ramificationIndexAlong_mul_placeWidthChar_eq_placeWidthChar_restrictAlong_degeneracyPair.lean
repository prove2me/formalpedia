-- Prove2me | Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidthChar_eq_placeWidthChar_restrictAlong_degeneracyPair
-- name    : ModularCurve.ramificationIndexAlong_mul_placeWidthChar_eq_placeWidthChar_restrictAlong_degeneracyPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/b00680d9-9cba-58f2-9d30-61d574fe4955
-- title:
--   Width transport along the degeneracy pair at supersingular places
-- statement:
--   Fix naturals $M, s, q'$ with $M, s \neq 0$, $s$ and $q'$ prime, $s \neq q'$ and $q' \nmid M$, and let $k$ be an algebraically closed field of characteristic $q'$. Write $F_N =$ `modularFunctionFieldC k N` for the intermediate field of $k((q))$ (Laurent series, `LaurentSeries k`) generated over $k$ by the series `jqModC k` and its $N$-fold $q$-expansion `jqNModC k N`, and recall that a `Place k F` is a valuation subring of $F$ containing the image of $k$, not equal to $F$, whose local ring is a principal ideal ring. The assertion is universally quantified over: maps $ab_i$ from the set `ssPlaces q' (M*s) k` of places $w$ of $F_{M\cdot s}$ satisfying `IsSupersingularPlace q' (M*s) k` to the corresponding set at level $M$ ($i \in \{0,1\}$); natural numbers $m_i(p)$ indexed by those places; two $k$-algebra homomorphisms $\varphi_0, \varphi_1 : F_M \to F_{M\cdot s}$, each assumed integral as a ring homomorphism, and pinned on $q$-expansions by requiring that $\varphi_0$ act as the identity on Laurent series and $\varphi_1$ as `qExpand k s`, i.e. $q \mapsto q^{s}$; together with the hypotheses that $ab_i(p)$ is the place of $F_M$ obtained by pulling back the valuation subring of $p$ along $\varphi_i$ (`Place.restrictAlong`) and that $m_i(p)$ is the ramification index of $p$ along $\varphi_i$, namely the least $n > 0$ of the form $\mathrm{ord}_p(\varphi_i f)$ for some $f \neq 0$ in $F_M$. Under these hypotheses, for every $i \in \{0,1\}$ and every such supersingular place $p$ at level $M\cdot s$, $$m_i(p) \cdot \mathrm{placeWidthChar}_{q', M\cdot s}(p) = \mathrm{placeWidthChar}_{q', M}(ab_i(p)),$$ where `placeWidthChar q' N w` is the natural-number quotient of `jWidthChar q' (w.evalAt (jGeomGen k N))` by `placeRamificationJ N w`; here `jWidthChar q' j` equals $12$ or $1$ according as $j = 0$ or not when $q' = 2$, equals $6$ or $1$ according as $j = 0$ or not when $q' = 3$, and equals `jWidth j` otherwise, and `placeRamificationJ N w` is the order at $w$ of `jGeomGen k N` minus its value at $w$, truncated to $\mathbb{N}$.
--
--   This is the comparison of widths of supersingular points at levels $M$ and $M\cdot s$ along the two degeneracy embeddings of modular function fields in characteristic $q'$: the width at the lower level is the ramification index times the width at the upper level. It is used in the analysis of the Hecke correspondence at supersingular places and in the gluing of specialisations of places across the two levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ramificationIndexAlong_mul_placeWidthChar_eq_placeWidthChar_restrictAlong_degeneracyPair.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
open AlgebraicCurve ModularCurve

theorem ModularCurve.ramificationIndexAlong_mul_placeWidthChar_eq_placeWidthChar_restrictAlong_degeneracyPair
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ (ab : Fin 2 → ↥(ssPlaces q' (M * s) k) → ↥(ssPlaces q' M k))
      (m : Fin 2 → ↥(ssPlaces q' (M * s) k) → ℕ)
      (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
      (hab : ∀ i p, (ab i p : Place k (modularFunctionFieldC k M))
        = Place.restrictAlong (φ i) (hφ i) ↑p)
      (hm : ∀ i p, m i p = Place.ramificationIndexAlong (φ i)
        (p : Place k (modularFunctionFieldC k (M * s)))),
    ∀ (i : Fin 2) (p : ↥(ssPlaces q' (M * s) k)),
      m i p * placeWidthChar q' (M * s)
          (p : Place k (modularFunctionFieldC k (M * s)))
        = placeWidthChar q' M (ab i p : Place k (modularFunctionFieldC k M)) := by sorry
