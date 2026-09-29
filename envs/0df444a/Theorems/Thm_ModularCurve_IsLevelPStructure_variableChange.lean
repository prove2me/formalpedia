-- Prove2me | Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange
-- name    : ModularCurve.IsLevelPStructure.variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/47f578ee-5a91-598b-9dde-219f259924a6
-- title:
--   Level-p data transport along Weierstrass variable changes
-- statement:
--   Let $A$ be a commutative ring, $W$ a Weierstrass curve over $A$, $p$ a natural number, and $D$ a term of the project's structure [`ModularCurve.LevelPData A`](def/ModularCurve_KatzLevelP.html#L43), i.e. a quadruple of elements $x_P, y_P, x_Q, y_Q$ of $A$. Assume the project's predicate [`ModularCurve.IsLevelPStructure W p D`](def/ModularCurve_KatzLevelP.html#L104), which asserts six things: the affine Weierstrass equation of $W$ holds at $(x_P,y_P)$ and at $(x_Q,y_Q)$; the $p$-th pre-division polynomial of $W$ vanishes at $x_P$ and at $x_Q$; and the two elements $\mathrm{indepElt}\,W\,p\,x_P\,x_Q$ and $\mathrm{indepElt}\,W\,p\,x_Q\,x_P$ are units, where $\mathrm{indepElt}\,W\,p\,x_0\,x = \prod_{a=1}^{(p-1)/2}\bigl(x\cdot(W.\Psi^2_a)(x_0) - (W.\Phi_a)(x_0)\bigr)$ with $(p-1)/2$ taken in natural-number division. Let $C = (u,r,s,t)$ be an admissible change of Weierstrass coordinates over $A$. Then the same six conditions hold for the curve $C \bullet W$ and the transported data $D.\mathrm{variableChange}\,C$, whose coordinates are $u^{-2}(x_P-r)$, $u^{-3}(y_P - s(x_P-r) - t)$ and likewise for $Q$; that is, [`ModularCurve.IsLevelPStructure (C • W) p (D.variableChange C)`](def/ModularCurve_KatzLevelP.html#L104) holds.
--
--   This is the functoriality of level-$p$ data in the sense used here under isomorphisms of Weierstrass models: the standard fact that a level structure on an elliptic curve transports along a change of coordinates, expressed in explicit division-polynomial coordinates. It guarantees that the transported data again satisfies the defining conditions, and so feeds the weight-$k$ transformation law for the associated level-$p$ modular forms and the many moduli-theoretic statements built on it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsLevelPStructure_variableChange.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.IsLevelPStructure.variableChange {A : Type*} [CommRing A] {W : WeierstrassCurve A} {p : ℕ}
    {D : ModularCurve.LevelPData A} (h : ModularCurve.IsLevelPStructure W p D)
    (C : WeierstrassCurve.VariableChange A) :
    ModularCurve.IsLevelPStructure (C • W) p (D.variableChange C) := by sorry
