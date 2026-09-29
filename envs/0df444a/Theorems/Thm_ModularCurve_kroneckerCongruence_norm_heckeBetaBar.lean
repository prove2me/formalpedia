-- Prove2me | Theorems.Thm_ModularCurve_kroneckerCongruence_norm_heckeBetaBar
-- name    : ModularCurve.kroneckerCongruence_norm_heckeBetaBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/f65de0f5-81fb-50f9-9db5-10c3d025c953
-- title:
--   Kronecker congruence at level N, norm form
-- statement:
--   Let $N\ge 1$, let $\ell$ be a prime not dividing $N$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $k$ has characteristic $\ell$. Write $F_M$ for [`ModularCurve.modularFunctionFieldBar M`](def/ModularCurve_ArithmeticGalois.html#L111), the intermediate field of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of the field $\mathbb Q(\text{divisorExpansions } M)\subset\mathbb Q((q))$; let $\alpha\colon F_N\to F_{N\ell}$ be `heckeAlphaBar`, the inclusion coming from the containment of these fields, and $\beta\colon F_N\to F_{N\ell}$ be `heckeBetaBar`, the substitution $q\mapsto q^{\ell}$ on Laurent series (`qExpand`, the exponent rescaling by $\ell$), and regard $F_{N\ell}$ as an $F_N$-algebra through $\alpha$. Let $y\in A((q))$ be such that its coefficientwise image $f$ in $\overline{\mathbb Q}((q))$ lies in $F_N$. Then there is $y'\in A((q))$ with two properties: its coefficientwise image in $\overline{\mathbb Q}((q))$ is the element of $F_N$ obtained as the algebra norm $N_{F_{N\ell}/F_N}(\beta(f))$; and its coefficientwise reduction $\bar y'\in k((q))$ equals the product of the coefficientwise $\ell$-th power (Frobenius) of $\bar y$ with $\bar y(q^{\ell})$, where $\bar y\in k((q))$ is the coefficientwise reduction of $y$.
--
--   This is the Kronecker congruence relation at level $N$ in norm ($q$-expansion) form: the norm of $f(q^{\ell})$ from level $N\ell$ down to level $N$ is integral and reduces modulo the maximal ideal of $A$ to $\bar f^{\,(\ell)}(q)\cdot\bar f(q^{\ell})$. It is used in the analysis of the reduction of the Hecke correspondence modulo $\ell$, being cited by [`ModularCurve.reductionModL_heckeOperatorBar`](thm.html#ModularCurve.reductionModL_heckeOperatorBar) and by the fibre-model computations of the Hecke divisor on cusp charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_kroneckerCongruence_norm_heckeBetaBar.lean

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.kroneckerCongruence_norm_heckeBetaBar (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (y : LaurentSeries A)
    (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar N) :
    ∃ y' : LaurentSeries A,
      ModularCurve.coeffMap A.subtype y' =
        ((letI := AlgebraicCurve.algebraAlong (ModularCurve.heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
          Algebra.norm (ModularCurve.modularFunctionFieldBar N)
            (ModularCurve.heckeBetaBar (AlgebraicClosure ℚ) N ℓ ⟨ModularCurve.coeffMap A.subtype y, hy⟩) :
            ModularCurve.modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ∧
      ModularCurve.coeffMap (IsLocalRing.residue A) y' =
        ModularCurve.coeffMap (frobenius (IsLocalRing.ResidueField A) ℓ)
            (ModularCurve.coeffMap (IsLocalRing.residue A) y) *
          ModularCurve.qExpand (IsLocalRing.ResidueField A) ℓ (ModularCurve.coeffMap (IsLocalRing.residue A) y) := by sorry
