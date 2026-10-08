-- Prove2me | Theorems.Thm_NegativeDP_Stationary_lemma31
-- name    : NegativeDP.Stationary.lemma31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:21.074797+00:00
-- url     : https://prove2.me/theorems/ef3941fd-b68e-4392-b5e8-cbc2dad65415
-- title:
--   Lemma 3.1 (N) — the n-stage returns decrease to the total return, Iₙ(π) ↓ I(π)
-- statement:
--   In the negative dynamic programming problem, let $\pi$ be any policy and $s$ any initial state. Let $I_n(\pi)=I_n(\pi,0)$ be the expected return of the first $n$ stages (terminal reward $0$) and $I(\pi)$ the expected total return. Then
--
--   $$I_n(\pi)(s)\ \downarrow\ I(\pi)(s)\qquad (n\to\infty),$$
--
--   that is, $n\mapsto I_n(\pi)(s)$ is non-increasing and converges to $I(\pi)(s)$ in $[-\infty,0]$.
--
--   The paper states Lemma 3.1 for the discounted, positive and negative cases; this item is the negative case. The lemma is the basic approximation of total returns by finite-horizon returns and is used in Theorems 4.1, 4.2 and 5.1.
--
--   **Formalization Note.** Returns lie in $[-\infty,0]$ and are minus sums of stage losses in $[0,\infty]$; convergence is in the order topology of the extended reals.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 875, Lemma 3.1 (N)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Lemma 3.1, case N (p. 875): `Iₙ(π) ↓ I(π)`, where `Iₙ(π) = Iₙ(π, 0)`. -/
theorem lemma31 (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    Antitone (fun n => In P π n 0 s) ∧
      Tendsto (fun n => In P π n 0 s) atTop (𝓝 (I P π s)) := by sorry

end NegativeDP.Stationary
