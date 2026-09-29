-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_relabel_smul_variableChange
-- name    : ModularCurve.LevelRelabelling.relabel_smul_variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/50fd7c01-06cd-5c2f-b9c7-2f110d7a416f
-- title:
--   Relabelling commutes with a Weierstrass change of variables
-- statement:
--   Let $T$ be a field, $W$ a Weierstrass curve over $T$ that is elliptic, $C$ a Weierstrass change of variables over $T$, $g$ a $2\times 2$ matrix with integer entries, and $D$ a level datum, i.e. a quadruple of elements $x_P,y_P,x_Q,y_Q$ of $T$. Write $\mathrm{toPoint}$ for the map sending a pair $(x,y)$ to the affine point $(x,y)$ of $W$ when it is nonsingular and to $0$ otherwise, $\mathrm{ofPoint}$ for the map sending $0$ to $(0,0)$ and an affine point $(x,y)$ to $(x,y)$, and $\mathrm{relabel}$ for the operation which, from $P=\mathrm{toPoint}(x_P,y_P)$ and $Q=\mathrm{toPoint}(x_Q,y_Q)$, forms the group-law combinations $g_{00}P+g_{10}Q$ and $g_{01}P+g_{11}Q$ and returns the level datum consisting of their coordinates under $\mathrm{ofPoint}$; and let $D^C$ denote the level datum with entries $u^{-2}(x-r)$, $u^{-3}(y-s(x-r)-t)$ applied to each of the two pairs of $D$. Assume that $(x_P,y_P)$ and $(x_Q,y_Q)$ both satisfy the affine Weierstrass equation of $W$, and that the two combinations $g_{00}P+g_{10}Q$ and $g_{01}P+g_{11}Q$ are nonzero in the group of affine points of $W$. Then relabelling the datum $D^C$ by $g$ on the curve $C\bullet W$ gives the same level datum as relabelling $D$ by $g$ on $W$ and then applying the change of variables $C$ to the resulting datum.
--
--   This is the coordinate-level statement that the integral relabelling $(P,Q)\mapsto(g_{00}P+g_{10}Q,\,g_{01}P+g_{11}Q)$ of a pair of affine points is equivariant for a Weierstrass change of variables, the nonvanishing hypotheses excluding the conventional junk value $(0,0)$ that $\mathrm{ofPoint}$ assigns to the point at infinity. It is used in the construction of level structures on modular curves, in particular in the full-level auxiliary lemmas producing sections and automorphisms compatible with relabelling.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_relabel_smul_variableChange.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Classical in

theorem ModularCurve.LevelRelabelling.relabel_smul_variableChange
    {T : Type} [Field T] (W : WeierstrassCurve T) [W.IsElliptic] (C : WeierstrassCurve.VariableChange T)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (D : ModularCurve.LevelPData T)
    (hP : W.toAffine.Equation D.xP D.yP) (hQ : W.toAffine.Equation D.xQ D.yQ)

    (h₁ : g 0 0 • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP + g 1 0 • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ ≠ 0)
    (h₂ : g 0 1 • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP + g 1 1 • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ ≠ 0) :
    ModularCurve.LevelRelabelling.LevelPData.relabel (C • W) g (D.variableChange C) =
      (ModularCurve.LevelRelabelling.LevelPData.relabel W g D).variableChange C := by sorry
