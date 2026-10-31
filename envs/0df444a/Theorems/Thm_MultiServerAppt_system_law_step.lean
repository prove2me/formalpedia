-- Prove2me | Theorems.Thm_MultiServerAppt_system_law_step
-- name    : MultiServerAppt.system_law_step
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:05:08.135999+00:00
-- url     : https://prove2.me/theorems/75e9c053-0395-4c3e-bd7e-56a632fe1d23
-- title:
--   Eq. (15) — the recursive step (corrected: $S^{(1)}=S$)
-- statement:
--   In the D/PH/s model, let $i+1\le m$. If the system law holds after client $s+i$, it holds after client $s+i+1$, with the vector
--
--   $$\alpha_{s+i+1}=f\big(p^{(s+i)}(x_{s+i+1}),\alpha\big)$$
--
--   of Eq. (15) and the matrix $S_{s+i+1}$.
--
--   With the base case, this gives the system law after every client.
--
--   Differences from the source:
--   - correction: printed start of the recursion S^(1) = 1 (p.12) → S^(1) = S, through Sblock; reason: the printed value is false: at s = 1, S = (-1), α = (1) it gives F_M(t) = 1 - e^t < 0
--   - reading: p_{j,(m_1,...,m_ξ)}(t) = P[(Y, Z) = (j, (m_1,...,m_ξ))] with Z a phase process (p.11) → SystemLaw: the joint law of Y and the residual services of the clients in service; reason: the model (6) has no phase process and the page does not fix slots; the Lean form determines the law of the multiset of phases, so nothing about the system law is dropped
--   - generalization: mean service time normalized to E B_i = 1 (p.9) → any PH(α, S) with S nonsingular; reason: the normalization is without loss of generality and the paper's case is an instance
--   - encoding: α holds initial probabilities; S^{-1} and finite means are used (pp.9, 10, 14) → ∑ α = 1 and IsUnit S.det are fields next to the published IsPHRep; reason: IsPHRep allows an atom at 0 and defective phases, which the source excludes; no instance of the source is lost
--   - encoding: states (j, m) and matrices ordered in blocks by j descending → a sum type of saturated and unsaturated states, indexed by i with N = s + i; reason: a Lean convention; block order does not matter to a function of states
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (15), p.14

import Mathlib
import Definitions.Def_MultiServerAppt_IsDPHSModel
import Definitions.Def_MultiServerAppt_SystemLaw

open MeasureTheory

namespace MultiServerAppt

/-- Eq. (15): if the system after client `s + i` follows `PH(α_{s+i}, S_{s+i})`, then the system after
client `s + i + 1` follows `PH(α_{s+i+1}, S_{s+i+1})`, with `α_{s+i+1}` given by the recursion (15).
Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (15), p.14. -/
theorem system_law_step {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {s m : ℕ} {α : ι → ℝ} {S : Matrix ι ι ℝ}
    {x : ℕ → ℝ} {B : ℕ → Ω → ℝ} (hM : IsDPHSModel P s m α S x B) (i : ℕ) (hi : i + 1 ≤ m)
    (hlaw : SystemLaw P s α S x B i) :
    SystemLaw P s α S x B (i + 1) := by sorry

end MultiServerAppt
