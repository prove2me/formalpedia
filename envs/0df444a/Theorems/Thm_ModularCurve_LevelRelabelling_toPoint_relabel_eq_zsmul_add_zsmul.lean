-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_toPoint_relabel_eq_zsmul_add_zsmul
-- name    : ModularCurve.LevelRelabelling.toPoint_relabel_eq_zsmul_add_zsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/71885635-2da0-5ed5-9ee7-f6b478f5a54f
-- title:
--   Relabelled level data read back as the relabelled points
-- statement:
--   Let $T$ be a field, $W$ a Weierstrass curve over $T$, $g$ a $2\times 2$ matrix with integer entries, and $D$ a `LevelPData T`, that is a quadruple $(x_P,y_P,x_Q,y_Q)$ of elements of $T$. Write $\mathrm{toPoint}\,W\,x\,y$ for the point of the group $W_{\mathrm{aff}}(T)$ equal to $(x,y)$ when $(x,y)$ is a nonsingular point of the affine model, and equal to the point at infinity $0$ otherwise, and set $P=\mathrm{toPoint}\,W\,x_P\,y_P$, $Q=\mathrm{toPoint}\,W\,x_Q\,y_Q$. Assume $g_{00}\cdot P+g_{10}\cdot Q\neq 0$ and $g_{01}\cdot P+g_{11}\cdot Q\neq 0$, the scalar multiplications being those of the abelian group $W_{\mathrm{aff}}(T)$. The relabelled data `LevelPData.relabel W g D` is by definition obtained by writing these two combinations back into coordinates via $\mathrm{ofPoint}$ (which sends $0$ to $(0,0)$ and an affine point to its pair of coordinates). The conclusion is that reading the relabelled data back as points recovers the combinations exactly: the first pair of `LevelPData.relabel W g D` gives $g_{00}\cdot P+g_{10}\cdot Q$ and the second pair gives $g_{01}\cdot P+g_{11}\cdot Q$.
--
--   This is the round-trip compatibility between the coordinate presentation of level data and the group law on the points of the affine Weierstrass model, for the right action of an integer $2\times2$ matrix on a pair of points (row-vector convention). It is used to transfer statements about relabelling of full-level structures, such as the determinant identities for the action on level data and the comparison with cusp data, from the coordinate currency of `LevelPData.relabel` to the currency of points in $W_{\mathrm{aff}}(T)$; the two non-vanishing hypotheses are needed because the coordinate pair $(0,0)$ assigned to the point at infinity need not itself lie on the curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_toPoint_relabel_eq_zsmul_add_zsmul.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.LevelRelabelling
open scoped Classical

theorem ModularCurve.LevelRelabelling.toPoint_relabel_eq_zsmul_add_zsmul
    {T : Type u} [Field T] (W : WeierstrassCurve T) (g : Matrix (Fin 2) (Fin 2) ℤ) (D : ModularCurve.LevelPData T)
    (hP : g 0 0 • toPoint W D.xP D.yP + g 1 0 • toPoint W D.xQ D.yQ ≠ 0)
    (hQ : g 0 1 • toPoint W D.xP D.yP + g 1 1 • toPoint W D.xQ D.yQ ≠ 0) :
    toPoint W (LevelPData.relabel W g D).xP (LevelPData.relabel W g D).yP =
        g 0 0 • toPoint W D.xP D.yP + g 1 0 • toPoint W D.xQ D.yQ ∧
      toPoint W (LevelPData.relabel W g D).xQ (LevelPData.relabel W g D).yQ =
        g 0 1 • toPoint W D.xP D.yP + g 1 1 • toPoint W D.xQ D.yQ := by sorry
