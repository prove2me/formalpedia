-- Prove2me | Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius
-- name    : ModularCurve.frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/b7489ee6-cb33-590f-8957-abca32c63856
-- title:
--   Geometric Frobenius carries the place of (W,C) to that of its twist
-- statement:
--   Let $\kappa$ be an algebraically closed field of prime characteristic $q'$, let $N\ge 1$ with $q'\nmid N$, let `data` be a modular polynomial datum at $q'$ (a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q')$ annihilating the pair $(j(q),j(q^{q'}))$) satisfying the Kronecker congruence $\Phi \bmod q' = (X^{q'}-Y)(X-Y^{q'})$, let $W$ be an elliptic Weierstrass curve over $\kappa$, and let $C$ be a cyclic subgroup of the group of affine points of $W$ with $\#C=N$. Write $F_N=\kappa(j(q),j(q^N))\subseteq\kappa((q))$ for `modularFunctionFieldC κ N`, and let $w$ be a place of $F_N$ over $\kappa$ (a valuation subring, not all of $F_N$, containing $\kappa$ and a principal ideal ring) whose valuation ring is the contraction along $F_N\hookrightarrow \kappa(j(q^d):d\mid N)$ of the valuation ring of the moduli place `moduliPlace κ N W C`. Then the valuation ring of `frobOnPlacesGeomLevel κ N data hKr w` — the transport of $w$ along the substitution $q\mapsto q^{q'}$, obtained by restricting $w$ to the image of $F_N$ under that substitution and identifying that image with $F_N$ — is the contraction along the same inclusion of the valuation ring of the moduli place of the Frobenius twist $W^{(q')}=$ `W.map (frobenius κ q')` together with the image of $C$ under the $q'$-power Frobenius on points.
--
--   This identifies the geometric Frobenius of the special fibre of $X_0(N)$ in characteristic $q'$ on moduli places: the point classified by a pair $(W,C)$ is sent to the pair $(W^{(q')},C^{(q')})$. It is used in the comparison of the Frobenius matrix on supersingular points with the Hecke matrix at $q'$ on the quaternionic class set in the Čerednik–Drinfeld part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve

theorem ModularCurve.frobOnPlacesGeomLevel_toValuationSubring_eq_comap_moduliPlace_map_frobenius
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q']
    (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (data : ModularPolynomialData q') (hKr : KroneckerCongruence q' data)
    (W : WeierstrassCurve κ) [W.IsElliptic]
    (C : AddSubgroup W.toAffine.Point) (hC : IsAddCyclic C) (hCN : Nat.card C = N)
    (w : Place κ ↥(modularFunctionFieldC κ N))
    (hw : w.toValuationSubring =
      (moduliPlace κ N W C).toValuationSubring.comap
        (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom) :
    (frobOnPlacesGeomLevel κ N data hKr w).toValuationSubring =
      (moduliPlace κ N (W.map (frobenius κ q'))
          (C.map (WeierstrassCurve.ratPointHom (frobenius κ q') (W₀ := W)))).toValuationSubring.comap
        (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom := by sorry
