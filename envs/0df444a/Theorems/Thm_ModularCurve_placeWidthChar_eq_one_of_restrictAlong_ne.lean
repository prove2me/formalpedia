-- Prove2me | Theorems.Thm_ModularCurve_placeWidthChar_eq_one_of_restrictAlong_ne
-- name    : ModularCurve.placeWidthChar_eq_one_of_restrictAlong_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/e878844f-05ac-58db-bf2f-4e35d4271883
-- title:
--   Width one at off-diagonal affine places of level Ms
-- statement:
--   Fix natural numbers $M, s, q'$ with $M, s$ nonzero, $s$ prime and $q'$ prime, and assume $s \neq q'$, $q' \nmid M$ and $s \nmid M$. Let $k$ be an algebraically closed field of characteristic $q'$. For a level $N$ write $F_N =$ `modularFunctionFieldC k N`, the intermediate field of the Laurent series field $k((q))$ generated over $k$ by `jqModC k` and its $N$-fold $q$-expansion twist `jqNModC k N`. The assertion is: for every pair $\varphi_0, \varphi_1$ of $k$-algebra embeddings $F_M \to F_{Ms}$ (indexed by `Fin 2`) such that both are integral as ring homomorphisms, $\varphi_0$ is the identity on underlying Laurent series, and $\varphi_1$ acts on underlying Laurent series as `qExpand k s` (the substitution multiplying Hahn-series exponents by $s$), and for every place $p$ of $F_{Ms}$ over $k$ (a proper valuation subring of $F_{Ms}$ containing the image of $k$ and which is a principal ideal ring), if the restrictions of $p$ along $\varphi_1$ and along $\varphi_0$ are distinct places of $F_M$, and if `placeRamificationJ (M * s) p`, the order at $p$ of `jGeomGen k (M * s)` minus its value $j_p$ at $p$, is positive, then `placeWidthChar q' (M * s) p = 1`; that is, the natural-number quotient of `jWidthChar q' j_p` by `placeRamificationJ (M * s) p` equals $1$, where `jWidthChar q' j` is $12$ or $1$ according as $j = 0$ or not when $q' = 2$, is $6$ or $1$ according as $j = 0$ or not when $q' = 3$, and is `jWidth j` otherwise.
--
--   This is the statement that, at an affine place of the level $Ms$ modular function field whose two degeneracy restrictions to level $M$ differ, the ramification over the $j$-line exhausts the characteristic-$q'$ width of the corresponding $j$-value; in moduli terms, the extra automorphisms of a triple $(E, C_M, C_s)$ beyond $\pm 1$ would force the two degeneracy images to agree. It feeds into [`ModularCurve.ramificationIndexAlong_heckeAlphaC_mul_placeRamificationJ_eq_jWidthChar_of_restrictAlong_ne_of_prime`](thm.html#ModularCurve.ramificationIndexAlong_heckeAlphaC_mul_placeRamificationJ_eq_jWidthChar_of_restrictAlong_ne_of_prime), part of the analysis of the special fibre of the modular curve of level $Ms$ in characteristic $q'$ used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_placeWidthChar_eq_one_of_restrictAlong_ne.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
open AlgebraicCurve ModularCurve

theorem ModularCurve.placeWidthChar_eq_one_of_restrictAlong_ne
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k] :
    ∀ (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x),
    ∀ p : Place k ↥(modularFunctionFieldC k (M * s)),
      Place.restrictAlong (φ 1) (hφ 1) p ≠ Place.restrictAlong (φ 0) (hφ 0) p →
      0 < placeRamificationJ (M * s) p →
      placeWidthChar q' (M * s) p = 1 := by sorry
