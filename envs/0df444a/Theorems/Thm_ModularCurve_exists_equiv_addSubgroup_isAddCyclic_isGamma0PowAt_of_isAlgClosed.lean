-- Prove2me | Theorems.Thm_ModularCurve_exists_equiv_addSubgroup_isAddCyclic_isGamma0PowAt_of_isAlgClosed
-- name    : ModularCurve.exists_equiv_addSubgroup_isAddCyclic_isGamma0PowAt_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/d652684b-6dde-50ad-9185-cae12bc43846
-- title:
--   Cyclic subgroups of order p^k match Γ₀-kernel polynomials
-- statement:
--   Let $F$ be an algebraically closed field with decidable equality, let $W$ be a Weierstrass curve over $F$ that is elliptic, let $p$ be a prime and $k \ge 1$ a natural number, and assume the image of $p$ in $F$ is nonzero. The assertion is that there exists a bijection $e$ between, on the one hand, the subtype of additive subgroups $H$ of the group $W.toAffine.Point$ of affine points of $W$ such that $H$ is additively cyclic and $\operatorname{card} H = p^k$, and, on the other hand, the subtype of polynomials $h \in F[X]$ satisfying [`ModularCurve.IsGamma0PowAt W p k h`](def/ModularCurve_WeierstrassGamma0Pow.html#L55), that is: if $p^k = 2$, then $\deg h \le 1$, the coefficient of $h$ in degree $1$ is $1$, and $h \mid W.\Psi_2^{\,2}$; while if $p^k \ne 2$, then $\deg h \le \varphi(p^k)/2$, the coefficient of $h$ in degree $\varphi(p^k)/2$ is $1$, $h \cdot W.preΨ(p^{k-1}) \mid W.preΨ(p^k)$, and $h \mid W.smulNumerator\,a\,(\varphi(p^k)/2)\,h$ for every natural $a$ with $2 \le a \le (p^k-1)/2$ and $p \nmid a$. Moreover the bijection is pinned down explicitly away from the case $p^k = 2$: for every such subgroup $H$, every point $Q$ with $H$ equal to the subgroup of integer multiples of $Q$, and provided $p^k \ne 2$, the polynomial $e(H)$ equals $\prod_{a} (X - C\,x(aQ))$, the product over $a \in [1, p^k/2]$ with $p \nmid a$, where $x(\cdot)$ denotes the first component of `coordsOrZero`, i.e. the $x$-coordinate of an affine point and $0$ at the point at infinity. No condition on $e$ is imposed when $p^k = 2$.
--
--   This is the statement that, over an algebraically closed field of residue characteristic different from $p$, the cyclic subgroups of order $p^k$ of an elliptic curve correspond bijectively to the $\Gamma_0(p^k)$-level structures in their polynomial (kernel-polynomial) form, the correspondence sending $\langle Q\rangle$ to the monic polynomial whose roots are the $x$-coordinates of the generators of $\langle Q\rangle$ up to sign. It feeds the count of tuples of such level structures in [`ModularCurve.natCard_isGamma0PowAt_tuple_eq_prod_of_isAlgClosed`](thm.html#ModularCurve.natCard_isGamma0PowAt_tuple_eq_prod_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_equiv_addSubgroup_isAddCyclic_isGamma0PowAt_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.exists_equiv_addSubgroup_isAddCyclic_isGamma0PowAt_of_isAlgClosed
    (F : Type) [Field F] [IsAlgClosed F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k) (hpF : ((p : ℕ) : F) ≠ 0) :
    ∃ e : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p ^ k} ≃
        {h : Polynomial F // ModularCurve.IsGamma0PowAt W p k h},
      ∀ (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p ^ k})
        (Q : W.toAffine.Point), AddSubgroup.zmultiples Q = H.1 → p ^ k ≠ 2 →
        ((e H : {h : Polynomial F // ModularCurve.IsGamma0PowAt W p k h}) : Polynomial F) =
          ∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
            (Polynomial.X - Polynomial.C ((a • Q).coordsOrZero).1) := by sorry
