-- Prove2me | Theorems.Thm_ModularCurve_IsLevelPStructure_relabel_variableChange
-- name    : ModularCurve.IsLevelPStructure.relabel_variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/c2baccc0-0c68-587a-af14-103ff0dad54b
-- title:
--   Relabelling level-ℓ data commutes with Weierstrass coordinate changes
-- statement:
--   Let $F$ be a field, $\ell$ a prime with $3 \le \ell$, and $W$ a Weierstrass curve over $F$ whose discriminant $W.\Delta$ is a unit. Let $D$ be a `LevelPData F`, that is a quadruple $(x_P,y_P,x_Q,y_Q)$ of elements of $F$, and assume `IsLevelPStructure W ℓ D`: the pairs $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine Weierstrass equation of $W$, the division polynomial $W.\mathrm{pre}\Psi\,\ell$ vanishes at $x_P$ and at $x_Q$, and both $\mathrm{indepElt}\,W\,\ell\,x_P\,x_Q$ and $\mathrm{indepElt}\,W\,\ell\,x_Q\,x_P$ are units, where $\mathrm{indepElt}\,W\,p\,x_0\,x=\prod_{a=1}^{(p-1)/2}\bigl(x\,(W.\Psi\mathrm{Sq}\,a)(x_0)-(W.\Phi\,a)(x_0)\bigr)$. Let $g$ be a $2\times 2$ integer matrix whose reduction modulo $\ell$ has unit determinant, and let $C=(u,r,s,t)$ be an admissible change of Weierstrass coordinates over $F$. The assertion is the equality of `LevelPData F`, i.e. of all four coordinates, between relabelling by $g$ on the curve $C \bullet W$ of the transported data $D^C$, and the transport by $C$ of the relabelling by $g$ of $D$ on $W$. Here transport is $x \mapsto u^{-2}(x-r)$, $y \mapsto u^{-3}(y-s(x-r)-t)$ applied to both pairs, and relabelling reads $(x_P,y_P)$, $(x_Q,y_Q)$ as points $P,Q$ of the affine point group (a non-nonsingular pair being read as $0$), forms $g_{00}P+g_{10}Q$ and $g_{01}P+g_{11}Q$, and writes their coordinates back, the point at infinity being written as $(0,0)$.
--
--   This is the compatibility of the $\mathrm{GL}_2(\mathbb{Z}/\ell)$-relabelling operation on Katz-style level-$\ell$ data with the action of changes of Weierstrass coordinates, the unit-determinant hypothesis on $g$ ensuring that no relabelled point degenerates to the point at infinity, whose coordinate convention $(0,0)$ is not preserved by transport. It is used in the construction of the natural relabelling of level-$\ell$ data, [`ModularCurve.LevelRelabelling.exists_natural_relabel_levelPData`](thm.html#ModularCurve.LevelRelabelling.exists_natural_relabel_levelPData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsLevelPStructure_relabel_variableChange.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.IsLevelPStructure.relabel_variableChange
    {F : Type u} [Field F] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (W : WeierstrassCurve F) (hΔ : IsUnit W.Δ) (D : LevelPData F) (hD : IsLevelPStructure W ℓ D)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det)
    (C : WeierstrassCurve.VariableChange F) :
    LevelRelabelling.LevelPData.relabel (C • W) g (D.variableChange C) =
      (LevelRelabelling.LevelPData.relabel W g D).variableChange C := by sorry
