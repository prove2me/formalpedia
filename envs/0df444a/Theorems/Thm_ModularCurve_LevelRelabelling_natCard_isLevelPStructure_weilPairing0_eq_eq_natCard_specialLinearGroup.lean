-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_natCard_isLevelPStructure_weilPairing0_eq_eq_natCard_specialLinearGroup
-- name    : ModularCurve.LevelRelabelling.natCard_isLevelPStructure_weilPairing0_eq_eq_natCard_specialLinearGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/88f75a58-3f2d-5544-94f0-0959d6d5831b
-- title:
--   Weil-normalised level-ℓ structures number #SL₂(ℤ/ℓ)
-- statement:
--   Let $K$ be an algebraically closed field, $W$ a Weierstrass curve over $K$ whose discriminant is a unit (so that $W$ is elliptic), and $\ell$ a prime with $3 \le \ell$ and $\ell \ne 0$ in $K$. A datum [`ModularCurve.LevelPData K`](def/ModularCurve_KatzLevelP.html#L43) is simply a quadruple $(x_P, y_P, x_Q, y_Q)$ of elements of $K$, and [`ModularCurve.IsLevelPStructure W ℓ D`](def/ModularCurve_KatzLevelP.html#L104) asserts that $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine Weierstrass equation of $W$, that $x_P$ and $x_Q$ are roots of $W.\mathrm{pre}\Psi\,\ell$, and that both $\mathrm{indepElt}\,W\,\ell\,x_P\,x_Q = \prod_{a=1}^{(\ell-1)/2}\bigl(x_Q\,(W.\Psi\mathrm{Sq}\,a)(x_P) - (W.\Phi\,a)(x_P)\bigr)$ and the same expression with $x_P$, $x_Q$ interchanged are units. Given one such datum $D_0$, the assertion is that the number of data $D$ which are level-$\ell$ structures for $W$ and for which $\mathrm{weilPairing0}\,W\,K\,\ell$ evaluated at the points $\mathrm{toPoint}(W_K, x_P, y_P)$ and $\mathrm{toPoint}(W_K, x_Q, y_Q)$ of $W$ base-changed to $K$ agrees with its value on $D_0$, equals the cardinality of $\mathrm{SL}_2(\mathbb{Z}/\ell)$. Here $\mathrm{toPoint}$ sends a pair of coordinates to the corresponding affine point when it is nonsingular and to $0$ otherwise, and $\mathrm{weilPairing0}\,W\,K\,n\,S\,T$ is the scalar $c \in K^\times$ by which translation by $S$ multiplies the Weil function $\mathrm{weilFun}\,W\,K\,n\,T$, taken to be $1$ if no such scalar exists.
--
--   This is the count of Weil-pairing-normalised Katz level-$\ell$ structures on an elliptic curve over an algebraically closed field: such structures are the ordered bases of the $\ell$-torsion with a prescribed pairing value, and they form a single free orbit under $\mathrm{SL}_2(\mathbb{Z}/\ell)$, whence the cardinality $\ell(\ell^2-1)$. It is used in the degree computation for the full level-$\ell$ modular curve, where the fibre over a moduli point is counted against the rational automorphisms of the curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_natCard_isLevelPStructure_weilPairing0_eq_eq_natCard_specialLinearGroup.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve WeierstrassCurve.Affine
open ModularCurve.LevelRelabelling
open scoped MatrixGroups

theorem ModularCurve.LevelRelabelling.natCard_isLevelPStructure_weilPairing0_eq_eq_natCard_specialLinearGroup
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓK : (ℓ : K) ≠ 0)
    (D₀ : ModularCurve.LevelPData K) (hD₀ : ModularCurve.IsLevelPStructure W ℓ D₀) :
    Nat.card {D : ModularCurve.LevelPData K // ModularCurve.IsLevelPStructure W ℓ D ∧
        weilPairing0 W K (ℓ : ℤ) (toPoint (W.baseChange K) D.xP D.yP) (toPoint (W.baseChange K) D.xQ D.yQ) = weilPairing0 W K (ℓ : ℤ) (toPoint (W.baseChange K) D₀.xP D₀.yP) (toPoint (W.baseChange K) D₀.xQ D₀.yQ)} =
    Nat.card (SL(2, ZMod ℓ)) := by sorry
