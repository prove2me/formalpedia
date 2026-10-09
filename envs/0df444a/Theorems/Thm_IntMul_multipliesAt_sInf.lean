-- Prove2me | Theorems.Thm_IntMul_multipliesAt_sInf
-- name    : IntMul.multipliesAt_sInf
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T08:49:22.622209+00:00
-- url     : https://prove2.me/theorems/9c312f65-aca4-48ed-ba12-3bb6f8572339
-- title:
--   The infimum of valid multiplication time budgets is attained
-- statement:
--   Let M be a deterministic multitape Turing machine in the shared IntMul model, and let n be a natural number. Suppose at least one finite real time budget permits M to multiply every pair of n-bit inputs correctly. Then the infimum of all valid budgets is itself a valid budget:
--
--   $$\operatorname{MultipliesAt}\!\left(M,n,\inf\{T\in\mathbb R:\operatorname{MultipliesAt}(M,n,T)\}\right).$$
--
--   For each input pair, any correct halting computation has a least natural-number halting time. Its admissible real budgets form a closed upper ray starting at that time. The set of uniform budgets is the intersection of these rays, is nonempty by hypothesis, and is bounded below by zero. Consequently its infimum belongs to it.
--
--   This supporting lemma justifies using the worst-case running time as a time budget in the shared Turing-machine formalization of the paper's complexity inequalities. It includes n = 0, and does not assume that a machine works at other input lengths.
-- source:
--   D. Harvey and J. van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193(2) (2021), 563-617, https://doi.org/10.4007/annals.2021.193.2.4; author preprint https://www.texmacs.org/joris/nlogn/nlogn.pdf, section 5.3, pp. 40-42.

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Definitions.Def_IntMul_MultitapeModel

open IntMul

/-- The worst-case time `sInf {τ | MultipliesAt M n τ}` is itself a valid budget. -/

theorem IntMul.multipliesAt_sInf {M : MultitapeTM} {n : ℕ} (h : ∃ τ, MultipliesAt M n τ) :
    MultipliesAt M n (sInf {τ : ℝ | MultipliesAt M n τ}) := by sorry
