-- Prove2me | Theorems.Thm_ModularCurve_coeffMap_residue_eq_C_mul_coeffMap_frobenius_of_qExpand_eq_C_mul_prod_qTwist
-- name    : ModularCurve.coeffMap_residue_eq_C_mul_coeffMap_frobenius_of_qExpand_eq_C_mul_prod_qTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/8eaef069-4a62-539b-9608-537d78bb06c2
-- title:
--   Mod-p reduction of a p-fold twisted product law
-- statement:
--   Let $p$ be a prime, $A$ a commutative local ring whose residue field $\kappa = \mathrm{ResidueField}(A)$ has characteristic $p$, let $\zeta \in A^\times$ satisfy $\zeta^p = 1$, let $u \in A$, and let $y, y_U$ be Laurent series over $A$. Here `qExpand A p` is the ring endomorphism of $A(\!(q)\!)$ obtained by transporting the support along multiplication by $p$ on $\mathbb{Z}$, i.e. the substitution $q \mapsto q^p$; `qTwist v` is the ring endomorphism multiplying the $k$-th coefficient by $v^k$ for a unit $v$; `HahnSeries.C r` is the Laurent series supported at $0$ with value $r$; and `coeffMap f` applies a ring homomorphism $f$ to every coefficient. Assume the product law $$y_U(q^p) \;=\; u \cdot \prod_{j=0}^{p-1} \mathrm{qTwist}(\zeta^j)(y)$$ in $A(\!(q)\!)$. The conclusion is the identity $$\overline{y_U} \;=\; \overline{u} \cdot \mathrm{coeffMap}\big(\mathrm{frobenius}\,\kappa\,p\big)\big(\overline{y}\big)$$ in $\kappa(\!(q)\!)$, where bars denote coefficientwise reduction along the residue map $A \to \kappa$; thus the reduction of $y_U$ is the constant $\overline u$ times the series obtained from $\overline y$ by raising each coefficient to the $p$-th power (no substitution $q \mapsto q^p$ on the right-hand side).
--
--   This is the algebraic half of the statement that, modulo the maximal ideal, a $p$-th-root function satisfying the $U_p$ product law over $A$ is intertwined with the coefficientwise Frobenius of $\kappa(\!(q)\!)$. It is used in the analysis of the model at $p$ of the modular curve, in the construction producing an integral element whose residue is a constant multiple of the coefficientwise Frobenius of the residue of a given Hecke-related element.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeffMap_residue_eq_C_mul_coeffMap_frobenius_of_qExpand_eq_C_mul_prod_qTwist.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.coeffMap_residue_eq_C_mul_coeffMap_frobenius_of_qExpand_eq_C_mul_prod_qTwist
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [IsLocalRing A] [CharP (IsLocalRing.ResidueField A) p]
    (ζ : Aˣ) (hζ : ζ ^ p = 1) (u : A) (y yU : LaurentSeries A)

    (hlaw : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      qExpand A p yU = HahnSeries.C u * ∏ j ∈ Finset.range p, qTwist (ζ ^ j) y) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    coeffMap (IsLocalRing.residue A) yU =
      HahnSeries.C (IsLocalRing.residue A u) * coeffMap (frobenius (IsLocalRing.ResidueField A) p) (coeffMap (IsLocalRing.residue A) y) := by sorry
