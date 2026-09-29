-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_isLevelPStructure
-- name    : ModularCurve.LevelRelabelling.variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_isLevelPStructure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/3fab0f0d-2c48-5eb3-8e6d-ad82d6b6e364
-- title:
--   Rigidity of Katz level-ℓ structures over algebraically closed fields
-- statement:
--   Let $K$ be an algebraically closed field (with decidable equality), and let $W$ be a Weierstrass curve over $K$ that is elliptic, so its discriminant $\Delta$ is a unit. Let $\ell$ be a prime with $3 \le \ell$ and with $\ell \ne 0$ in $K$. Let $D$ be level-$\ell$ data, that is, a quadruple $(x_P, y_P, x_Q, y_Q)$ of elements of $K$, and assume [`ModularCurve.IsLevelPStructure W ℓ D`](def/ModularCurve_KatzLevelP.html#L104): the pairs $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine Weierstrass equation of $W$; the polynomial `W.preΨ ℓ` vanishes at $x_P$ and at $x_Q$; and both products $\prod_{a=1}^{(\ell-1)/2}\bigl(x_Q\,(W.\mathrm{\Psi Sq}\,a)(x_P) - (W.\Phi\,a)(x_P)\bigr)$ and the same expression with $x_P$ and $x_Q$ interchanged are units in $K$. Finally let $C = (u,r,s,t)$ be a Weierstrass variable change over $K$ with $C \bullet W = W$ and with $D$ fixed by $C$, i.e. $u^{-2}(x_P - r) = x_P$, $u^{-3}(y_P - s(x_P-r) - t) = y_P$ and likewise for $(x_Q,y_Q)$. The conclusion is that $C = 1$, that is $(u,r,s,t) = (1,0,0,0)$.
--
--   This is the rigidity statement that the automorphism group of a Weierstrass model acts freely on level-$\ell$ structures for $\ell \ge 3$ invertible, in the coordinate form used for Katz level structures; it fails for $\ell = 2$, where $[-1]$ fixes $E[2]$. It feeds the orbit–stabiliser count relating the number of maximal level structures, the order of the rational automorphism group and the order of $\mathrm{SL}_2$ over the residue ring at a moduli place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_isLevelPStructure.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve.Affine
open scoped MatrixGroups

theorem ModularCurve.LevelRelabelling.variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_isLevelPStructure
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓK : (ℓ : K) ≠ 0)
    (D : ModularCurve.LevelPData K) (hD : ModularCurve.IsLevelPStructure W ℓ D)
    (C : WeierstrassCurve.VariableChange K) (hCW : C • W = W) (hCD : D.variableChange C = D) :
    C = 1 := by sorry
