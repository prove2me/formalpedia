-- Prove2me | Theorems.Thm_Helfgott_moebius_reciprocal_decay_of_finite_certificate
-- name    : Helfgott.moebius_reciprocal_decay_of_finite_certificate
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:16:21.40198+00:00
-- url     : https://prove2.me/theorems/80d7fe2a-3f34-46df-bbd3-e17bbf715ff7
-- title:
--   Sound finite integer certificate for reciprocal Mobius decay
-- statement:
--   Let $2\le A$, $B\le1200001$ and $Q>0$ be integers. Suppose a candidate Möbius table and a rounded reciprocal-sum certificate both have capacity at least $B$. Assume that the Möbius prime-factor checker succeeds, the reciprocal certificate starts at zero, and every reciprocal recurrence, endpoint join, integer inequality and logarithm-tier check succeeds. Then the actual Möbius function satisfies $$\left|\sum_{1\le n\le\lfloor x\rfloor}\frac{\mu(n)}n\right|\le\frac{0.03}{\log x}\qquad(A\le x<B).$$ This supplies the complete logical reduction of the finite reciprocal-decay input to exact integer checks. Concrete candidate tables must be checked separately.
-- source:
--   Original complete finite integer certificate soundness proof for reciprocal Mobius decay in the Helfgott minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusReciprocalCertificate
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_Helfgott_MobiusFiniteCertificate
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
open Finset Nat ArithmeticFunction Real
open scoped BigOperators

namespace Helfgott

theorem moebius_reciprocal_decay_of_finite_certificate 
    (A B Q dm dr : ℕ) (muTree : MobiusCertTree) (rTree : MobiusReciprocalTree)
    (hA : 2 ≤ A) (hB : B ≤ 1200001) (hQ : 0 < Q)
    (hmCapacity : B ≤ 32 * 2 ^ dm) (hrCapacity : B ≤ 32 * 2 ^ dr)
    (hm : mobiusTreeCheck (mobiusTreeValue dm muTree) B dm 0 muTree = true)
    (hstart : mobiusReciprocalStart rTree = 0)
    (hr : mobiusReciprocalTreeCheck (mobiusTreeValue dm muTree) Q A B dr 0 rTree = true) :
    ∀ x : ℝ, (A : ℝ) ≤ x → x < (B : ℝ) →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
        (3 / 100 : ℝ) / Real.log x := by sorry

end Helfgott
