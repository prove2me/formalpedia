-- Prove2me | Theorems.Thm_MultiServerAppt_system_law_base
-- name    : MultiServerAppt.system_law_base
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:05:29.591982+00:00
-- url     : https://prove2.me/theorems/226e7e95-cc85-4062-a5dc-1cba6d150e0a
-- title:
--   Eq. (11) — the base case (corrected: $S^{(1)}=S$)
-- statement:
--   In the D/PH/s model, the system after the first $s$ clients is described by $\mathrm{PH}(\alpha_s,S_s)$:
--
--   $$p^{(s)}(t)=\big(p_s^{(s)}(t),p_{s-1}^{(s)}(t),\dots,p_1^{(s)}(t)\big)=\alpha_s\exp(S_st).$$
--
--   Precisely, the predicate `SystemLaw` holds at $i=0$.
--
--   It is the start of the recursion: all servers are busy, nobody waits, and the system only empties.
--
--   Differences from the source:
--   - correction: printed start of the recursion S^(1) = 1 (p.12) → S^(1) = S, through Sblock; reason: the printed value is false: at s = 1, S = (-1), α = (1) it gives F_M(t) = 1 - e^t < 0
--   - reading: p_{j,(m_1,...,m_ξ)}(t) = P[(Y, Z) = (j, (m_1,...,m_ξ))] with Z a phase process (p.11) → SystemLaw: the joint law of Y and the residual services of the clients in service; reason: the model (6) has no phase process and the page does not fix slots; the Lean form determines the law of the multiset of phases, so nothing about the system law is dropped
--   - generalization: mean service time normalized to E B_i = 1 (p.9) → any PH(α, S) with S nonsingular; reason: the normalization is without loss of generality and the paper's case is an instance
--   - encoding: α holds initial probabilities; S^{-1} and finite means are used (pp.9, 10, 14) → ∑ α = 1 and IsUnit S.det are fields next to the published IsPHRep; reason: IsPHRep allows an atom at 0 and defective phases, which the source excludes; no instance of the source is lost
--   - encoding: states (j, m) and matrices ordered in blocks by j descending → a sum type of saturated and unsaturated states, indexed by i with N = s + i; reason: a Lean convention; block order does not matter to a function of states
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (11), p.12

import Mathlib
import Definitions.Def_MultiServerAppt_IsDPHSModel
import Definitions.Def_MultiServerAppt_SystemLaw

open MeasureTheory

namespace MultiServerAppt

/-- Eq. (11): the law of the system after the first `s` clients is described by `PH(α_s, S_s)`.
Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (11), p.12. -/
theorem system_law_base {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {s m : ℕ} {α : ι → ℝ} {S : Matrix ι ι ℝ}
    {x : ℕ → ℝ} {B : ℕ → Ω → ℝ} (hM : IsDPHSModel P s m α S x B) :
    SystemLaw P s α S x B 0 := by sorry

end MultiServerAppt
