-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_interval_search
-- name    : MinimaxInterventions1429.Separable.interval_search
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:09.871936+00:00
-- url     : https://prove2.me/theorems/9b24e080-3c50-4fc2-826c-f05b8b32ce9e
-- title:
--   Lemma 3.1 — interval search
-- statement:
--   Let $x\in[-1,1]$, let $\psi\ge0$, and let $T\ge1$ be an integer. Run the actual interval recurrence from $[-1,1]$ for $T$ bits. At each realized midpoint $t$, suppose bit $1$ implies $x\le t+\psi$ and bit $0$ implies $x\ge t-\psi$. If $\widehat x$ is its clipped final midpoint, then
--
--   $$\widehat x\in[-1,1],\qquad |\widehat x-x|\le\psi+2^{-T}.$$
--
--   The implications are required only for the actual returned bits and thresholds. The statement supplies the finite-precision comparison bound used for both contrast and row-level searches.
--
--   Differences from the source:
--   - encoding: T comparison steps with x in [-1,1] and nonnegative slack → a list of exactly T bits with its recursively computed prefix thresholds; reason: this is the literal adaptive interval recurrence evaluated on its observed bit list
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Lemma 3.1, printed p.10 (PDF p.12)

import Definitions.Def_MinimaxInterventions1429_Separable_ObservationLaws
set_option autoImplicit false

namespace MinimaxInterventions1429.Separable

theorem interval_search (x ψ : ℝ) (T : ℕ) (hT : 1 ≤ T)
    (hx : -1 ≤ x ∧ x ≤ 1) (hψ : 0 ≤ ψ) (bits : List Bool) (hlen : bits.length = T)
    (hbits : ∀ i : Fin bits.length,
      let t := intervalThreshold ψ (bits.take i.val)
      if bits.get i then x ≤ t + ψ else t - ψ ≤ x) :
    -1 ≤ intervalEstimate ψ bits ∧ intervalEstimate ψ bits ≤ 1 ∧
      |intervalEstimate ψ bits - x| ≤ ψ + eta T := by sorry

end MinimaxInterventions1429.Separable
