-- Prove2me | Theorems.Thm_MasulloRH_translated_shell_weight_requires_width_plus_twist_at_least_one
-- name    : MasulloRH.translated_shell_weight_requires_width_plus_twist_at_least_one
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T04:39:30.367426+00:00
-- url     : https://prove2.me/theorems/253e2820-f698-4f31-8af1-176210b3731c
-- title:
--   A translated radial nuclear trace can supply prime weight exponent β only when band half-width plus β reaches one
-- statement:
--   Let $\alpha,\beta\ge0$ with $\alpha+\beta<1$. Set $W_\alpha(x)=e^{\alpha |x|}(1+x^2)$ in log norm. Take any fixed nuclear kernel expansion in $L^2(dx)$ with measurable factors $F_j,G_j$ and finite projective cost, and any complex shell masks $m_{n,p}(x)$ with $\sum_p|m_{n,p}(x)|\le 1$. Write $d_n$ for its diagonal after weighted output translation by $u_n=n\log2$, namely $d_n(x)=[W_\alpha(x)/W_\alpha(x-u_n)]\sum_j F_j(x-u_n)G_j(x)$. For arbitrarily large $n$ some prime $2^n\le p<2^{n+1}$ satisfies $|\int m_{n,p}d_n\,dx|<2^{-\beta(n+1)}$. In particular a half-weight $p^{-1/2}\log p$ in a dyadic flat-top test is incompatible with this nuclear-diagonal construction at every positive band half-width below $1/2$. The necessary condition leaves equality $\alpha+\beta=1$ undecided.
-- source:
--   Masullo, The Music of the Primes, frozen 20 November 2026, (9.2.2.41), (9.3.1.2), (10.4.3.45–50), (11.3.2.1–5). Extends Prove2Me 76519aa9-434d-4558-9eb8-ed111d354e4a to the half-twisted candidate from 7a3ddce5-168d-4a1a-bb7c-60732b37a05f. Uses the normalized double angular shell mass db985081-fca8-4440-bfd1-276f6e60b4e6.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Finset Filter MeasureTheory
open scoped ENNReal Topology

theorem MasulloRH.translated_shell_weight_requires_width_plus_twist_at_least_one (α β : ℝ) (hα : 0 ≤ α) (_hβ : 0 ≤ β) (hcrit : α + β < 1)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ j, Measurable (f j)) (hg : ∀ j, Measurable (g j))
    (hcost : (∑' j, eLpNorm (f j) 2 volume * eLpNorm (g j) 2 volume) ≠ ∞)
    (m : ℕ → Nat.Primes → ℝ → ℂ) (hm : ∀ n p, Measurable (m n p))
    (hpart : ∀ n x, ∑' p, ‖m n p x‖ₑ ≤ 1) :
    let W := fun x : ℝ => Real.exp (α*|x|) * (1+x^2)
    let u := fun n : ℕ => (n:ℝ)*Real.log 2
    ∀ N : ℕ, ∃ (n : ℕ) (p : Nat.Primes), (p:ℕ).log2 = n ∧ N ≤ n ∧
      ‖∫ x : ℝ, m n p x * ∑' j, ((W x / W (x-u n) : ℝ) : ℂ) * f j (x-u n) * g j x‖ₑ <
       ENNReal.ofReal (Real.exp (-β * u (n+1))) := by sorry
