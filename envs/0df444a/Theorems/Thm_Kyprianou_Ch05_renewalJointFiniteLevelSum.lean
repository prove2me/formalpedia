-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalJointFiniteLevelSum
-- name    : Kyprianou.Ch05.renewalJointFiniteLevelSum
-- status  : Open
-- author  : @DAGA
-- created : 2026-11-26T03:06:59.369672+00:00
-- url     : https://prove2.me/theorems/e84ae796-6e29-5d5a-8b04-d80d7d2bea9f
-- title:
--   Lemma 5.5 step: joint over/undershoot law as a sum over epochs
-- statement:
--   Fix a level $x > 0$ and measurable sets $A \subseteq (0, \infty)$ and $B \subseteq (0, x]$. The joint event that the overshoot $R_x = S_{N_x} - x$ is positive, lies in $A$, and the undershoot $V_x = x - S_{N_x - 1}$ lies in $B$ decomposes over the value of the first passage index $N_x = n + 1$. On the $n$-th piece the last epoch below the level is $S_n = v \le x$ and the crossing spacing is $Z_n = z > x - v$, with $z - (x - v) \in A$ and $x - v \in B$. By the one-step independence of $Z_n$ from $S_n$ and the fact that $S_n$ has law $F^{*n}$, the $n$-th piece has probability $\int_{v \in [0, x]} \int_{z > x - v} \mathbf{1}\{z - (x-v) \in A,\ x - v \in B\} \, dF(z) \, dF^{*n}(v)$, and nonexplosion of the epochs makes the pieces exhaust the event up to a null set. Summing over $n$ gives the stated identity.
-- source:
--   Kyprianou (2006), first edition, Lemma 5.5, printed pp.116-117, equation (5.5).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05
open Classical in
theorem renewalJointFiniteLevelSum
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat -> Omega -> Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (x : Real) (hx : 0 < x)
    (A B : Set Real) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA2 : A ⊆ Set.Ioi (0 : Real)) (hB2 : B ⊆ Set.Ioc (0 : Real) x) :
    P {omega : Omega |
      0 < renewalOvershoot Z x omega ∧
      renewalOvershoot Z x omega ∈ A ∧
      renewalUndershoot Z x omega ∈ B} =
    ∑' n : Nat, ∫⁻ v in Set.Icc (0 : Real) x,
      (∫⁻ z in Set.Ioi (x - v),
        (if z - (x - v) ∈ A ∧ x - v ∈ B then (1 : ENNReal) else 0) ∂F)
      ∂(renewalConvolutionPower F n) := by
  sorry
end Kyprianou.Ch05
