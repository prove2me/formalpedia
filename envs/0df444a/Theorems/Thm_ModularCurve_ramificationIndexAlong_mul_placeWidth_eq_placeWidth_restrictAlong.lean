-- Prove2me | Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong
-- name    : ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/95700e66-148c-5b7d-a554-e3b776bd78e4
-- title:
--   Width transport along both degeneracy maps at every place
-- statement:
--   Let $M,s,q'$ be natural numbers with $M\neq 0$, $s\neq 0$, $s$ and $q'$ prime, $s\neq q'$ and $q'\nmid M$, and let $k$ be an algebraically closed field of characteristic $q'$. Write $F_N=$ `modularFunctionFieldC k N` for the intermediate field of $k((q))$ generated over $k$ by `jqModC k` and its $N$-fold $q$-substitution `qExpand k N (jqModC k)`, and $j_N=$ `jGeomGen k N` for the element `jqModC k` of $F_N$. The assertion is: for every family $\varphi:\mathrm{Fin}\,2\to (F_M\to_{\mathrm{alg}[k]}F_{M\cdot s})$ such that each $\varphi_i$ is integral as a ring map, $\varphi_0$ is the identity on underlying Laurent series, and $\varphi_1$ sends $x$ to `qExpand k s x`, for each $i\in\{0,1\}$ and each place $p$ of $F_{M\cdot s}$ over $k$ (a proper valuation subring containing $k$ whose ring is a principal ideal ring) such that `placeRamificationJ (M*s) p`, the truncation to $\mathbb{N}$ of $\mathrm{ord}_p(j_{M\cdot s}-p(j_{M\cdot s}))$, divides $\mathrm{jWidth}(p(j_{M\cdot s}))$ (where $\mathrm{jWidth}(j)$ is $3$, $2$, $1$ according as $j=0$, $j=1728$, otherwise), one has $$e_{\varphi_i}(p)\cdot\mathrm{placeWidth}(M\cdot s,p)=\mathrm{placeWidth}(M,\ p|_{\varphi_i}),$$ with $e_{\varphi_i}(p)$ the ramification index of $p$ for the algebra structure on $F_{M\cdot s}$ over $F_M$ given by $\varphi_i$, $p|_{\varphi_i}$ the valuation subring pulled back along $\varphi_i$, and $\mathrm{placeWidth}(N,w)=\mathrm{jWidth}(w(j_N))/\mathrm{placeRamificationJ}\,N\,w$ in natural-number division.
--
--   This is the transport rule for the widths of the points of the modular curve of level $M\cdot s$ in characteristic $q'$ along the two degeneracy embeddings (identity and $q\mapsto q^s$ on $q$-expansions), the local bookkeeping that compares the width of a point with the width of its images on the level-$M$ curve. It is used in the computations of Hecke and degeneracy matrices on the supersingular module at level $M\cdot s$, where widths enter the adjointness and companion relations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve ModularCurve

theorem ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x),
    ∀ (i : Fin 2) (p : Place k (modularFunctionFieldC k (M * s))),
      placeRamificationJ (M * s) p ∣ jWidth (p.evalAt (jGeomGen k (M * s))) →
      Place.ramificationIndexAlong (φ i) p * placeWidth (M * s) p
        = placeWidth M (Place.restrictAlong (φ i) (hφ i) p) := by sorry
