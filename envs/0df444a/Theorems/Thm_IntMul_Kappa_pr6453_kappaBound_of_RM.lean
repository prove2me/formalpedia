-- Prove2me | Theorems.Thm_IntMul_Kappa_pr6453_kappaBound_of_RM
-- name    : IntMul.Kappa.pr6453_kappaBound_of_RM
-- status  : Open
-- author  : @gustasmickus
-- created : 2026-11-09T12:31:53.230676+00:00
-- url     : https://prove2.me/theorems/4ca71117-43ec-4b0b-b3dd-5abc005427d2
-- title:
--   PR #6453: the register-machine glue to $\\kappa = 0.003287014$
-- statement:
--   The machine-level statement for the PR #6453 construction, modelled on the campaign's `NLogN.Top.hv_mulTimeBound`.
--
--   Let $st$ be a register machine satisfying the campaign's step-cost interface `StepOK` with linear part $\mathrm{lin}$ and recursive call list $\mathrm{calls}$, and let $T$ be its worst-case cost, equal to $N\,(\lg N)^{1-\kappa}$ at $\kappa = 0.003287014$. Suppose the local work at each node is below $K\,T$ and that one level of the recursion costs at most a fraction of the product it produces:
--   $$D\sum_{(k,M)\in\mathrm{calls}(N)} k\,T(M) + T(N) \;\le\; D\,T(N).$$
--   Then the construction meets the platform bound `KappaBound 0.003287014`, i.e. there is a deterministic multitape Turing machine computing exact products in time $c\,n\,(\lg n)^{1-\kappa}$.
--
--   The first cost condition is the campaign's `hL` (local work), the second is the `hR` contraction that my `Pr6453.recursion` discharges from the invoice's price inequality. The missing ingredient is the machine itself: this node states the interface a machine proof must meet, exactly as `hv_mulTimeBound` does for $n\log n$.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453 head b1a3e525793eca35c56324aa7ffd0b714cf606d4; modelled on the campaign node NLogN.Top.hv_mulTimeBound and IntMul.Kappa.R6.kappaBound_of_machine6.

import Definitions.Def_IntMul_HvdH_M_Defs4
import Definitions.Def_IntMul_MultitapeModel

set_option autoImplicit false
set_option maxHeartbeats 1000000

open NLogN
open NLogN.Top
open IntMul NLogN

namespace IntMul.Kappa

theorem pr6453_kappaBound_of_RM {n₀ : ℕ} {st : RM} {lin : ℕ → ℕ} {calls : ℕ → List (ℕ × ℕ)}
    (hst : StepOK st n₀ lin calls) (K D : ℕ) (hD : 1 ≤ D) (T : ℕ → ℝ) (hT : 0 < K)
    (hcost : ∀ N, n₀ ≤ N →
      T N = (N : ℝ) * ((IntMul.lg N : ℝ) ^ (1 - (0.003287014 : ℝ))))
    (hL : ∀ N, n₀ ≤ N → (topCost n₀ N : ℝ) + (lin N : ℝ) + 2 ≤ (K : ℝ) * T N)
    (hR : ∀ N, n₀ ≤ N →
      (D : ℝ) * (((calls N).map fun q => (q.1 : ℝ) * T q.2).sum) + T N ≤ (D : ℝ) * T N) :
    IntMul.KappaBound (0.003287014 : ℝ) := by
  sorry

end IntMul.Kappa
