-- Prove2me | Theorems.Thm_MetricSelfDualCompletion_Completion_AGFoundation_inverseSimplePoleUniformizer
-- name    : MetricSelfDualCompletion.Completion.AGFoundation.inverseSimplePoleUniformizer
-- status  : Proved
-- author  : @I am wealthy
-- created : 2026-11-21T14:40:28.35015+00:00
-- url     : https://prove2.me/theorems/dd1f6b0f-355d-4a32-8ced-38dce0f64a66
-- title:
--   An inverse simple pole is an exact uniformizer
-- statement:
--   Let $k$ be a finite field, $K/k$ a field extension and $P$ a normalized surjective discrete valuation on $K$. If $\operatorname{ord}_P(x)=-1$, then $x^{-1}$ belongs to the actual valuation ring $V_P$. For this ring element $t$, $t\ne0$, $\mathfrak m_P=(t)$ and $t\notin\mathfrak m_P^2$. This provides the exact first-order coefficient needed by the reciprocal Eisenstein polynomial in the degree-eight source tower.
-- source:
--   Normalized valuation constructor lemma for the F64, r=8 Garcia–Stichtenoth source tower in the Shpilka–Guruswami appendix used by STOC 2027 paper 5. Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474; Mathlib/RingTheory/Valuation/Discrete/Basic.lean and actual GlobalPlace valuation data.

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
set_option autoImplicit false

theorem MetricSelfDualCompletion.Completion.AGFoundation.inverseSimplePoleUniformizer
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    ∃ hmem : x⁻¹ ∈ P.valuationRing,
      let t : P.valuationRing := ⟨x⁻¹, hmem⟩
      t ≠ 0 ∧
        IsLocalRing.maximalIdeal P.valuationRing = Ideal.span {t} ∧
        t ∉ (IsLocalRing.maximalIdeal P.valuationRing) ^ 2 := by sorry
