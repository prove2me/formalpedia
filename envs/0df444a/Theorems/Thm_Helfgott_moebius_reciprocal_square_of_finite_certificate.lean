-- Prove2me | Theorems.Thm_Helfgott_moebius_reciprocal_square_of_finite_certificate
-- name    : Helfgott.moebius_reciprocal_square_of_finite_certificate
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:29:00.928614+00:00
-- url     : https://prove2.me/theorems/da1fe6f1-77b2-4a3e-b9f5-311a495fe1d7
-- title:
--   Soundness of the finite reciprocal Mobius square-root certificate
-- statement:
--   Let the fixed candidate Mobius tree and rounded reciprocal tree pass their exact Boolean checks through an integer B at most 1200001, with positive integer scale Q and sufficient tree capacities. Suppose the reciprocal tree starts at zero. Then for the actual Mobius function, $$x\left(\sum_{1\le n\le\lfloor x\rfloor}\frac{\mu(n)}n\right)^2\le2\quad(1\le x<B).$$ Every integer at least 2 is checked with the stronger inequality $(|S_n|+n)^2(n+1)\le2Q^2$. The floor interval at 1 is handled exactly. The Boolean certificate hypotheses are explicit and must be supplied separately.
-- source:
--   Original exact integer-rounding and real-floor soundness proof for the finite reciprocal Mobius square-root bound. Written by Codex.

import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
import Definitions.Def_Helfgott_MobiusFiniteCertificate
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators

namespace Helfgott
theorem moebius_reciprocal_square_of_finite_certificate
    (B Q dm dr : ℕ) (muTree : MobiusCertTree) (rTree : MobiusReciprocalTree)
    (hB : B ≤ 1200001) (hQ : 0 < Q)
    (hmCapacity : B ≤ 32*2^dm) (hrCapacity : B ≤ 32*2^dr)
    (hm : mobiusTreeCheck (mobiusTreeValue dm muTree) B dm 0 muTree = true)
    (hstart : mobiusReciprocalStart rTree = 0)
    (hr : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue dm muTree) Q B dr 0 rTree = true) :
    ∀ x : ℝ, 1 ≤ x → x < (B : ℝ) →
      (∑ n∈Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ)/(n : ℝ))^2*x ≤ 2 := by sorry
end Helfgott
