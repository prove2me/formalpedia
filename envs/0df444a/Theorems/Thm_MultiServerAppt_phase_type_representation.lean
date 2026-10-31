-- Prove2me | Theorems.Thm_MultiServerAppt_phase_type_representation
-- name    : MultiServerAppt.phase_type_representation
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:01:38.530129+00:00
-- url     : https://prove2.me/theorems/b6cfc612-8200-4fc8-b3bc-6eb2d48e669f
-- title:
--   $(\alpha_{s+i},S_{s+i})$ is a phase-type representation (corrected: $S^{(1)}=S$)
-- statement:
--   Let $s\ge 1$, let $(\alpha,S)$ be a phase-type representation with $\sum_a\alpha_a=1$ and $S$ nonsingular, and let $x_{s+l}\ge 0$ for $1\le l\le m$. Then for $0\le i\le m$, $\alpha_{s+i}$ is a probability vector, $S_{s+i}$ is a phase-type generator, and $S_{s+i}$ is nonsingular.
--
--   This makes the expressions $\exp(S_{s+i}t)$ and $S_{s+i}^{-1}$ of §4.2 meaningful for an absorption time.
--
--   Differences from the source:
--   - correction: printed start of the recursion S^(1) = 1 (p.12) → S^(1) = S, through Sblock; reason: the printed value is false: at s = 1, S = (-1), α = (1) it gives F_M(t) = 1 - e^t < 0
--   - generalization: mean service time normalized to E B_i = 1 (p.9) → any PH(α, S) with S nonsingular; reason: the normalization is without loss of generality and the paper's case is an instance
--   - encoding: α holds initial probabilities; S^{-1} and finite means are used (pp.9, 10, 14) → ∑ α = 1 and IsUnit S.det are fields next to the published IsPHRep; reason: IsPHRep allows an atom at 0 and defective phases, which the source excludes; no instance of the source is lost
--   - encoding: states (j, m) and matrices ordered in blocks by j descending → a sum type of saturated and unsaturated states, indexed by i with N = s + i; reason: a Lean convention; block order does not matter to a function of states
--   - generalization: i ∈ {1, …, n − s} (p.13) → 0 ≤ i ≤ m; reason: i = 0 is (α_s, S_s) of Eq. (11), p.12, which the page also calls a phase-type distribution; the page's range is an instance
--   - encoding: a phase-type distribution (α_{s+i}, S_{s+i}), with S_{s+i}^{-1} used on p.15 → IsPHRep, ∑ α_{s+i} = 1 and IsUnit (det S_{s+i}); reason: what the page's use of exp(S_{s+i} t) as an absorption law and of S_{s+i}^{-1} presupposes; no instance of the source is lost
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eqs. (8), (13), pp.12-13, and Eq. (15), p.14

import Mathlib
import Definitions.Def_MultiServerAppt_alphaSys

open Matrix

namespace MultiServerAppt

/-- `(α_{s+i}, S_{s+i})` is a phase-type representation, for `0 ≤ i ≤ m`: `α_{s+i}` is a probability
vector and `S_{s+i}` is a nonsingular phase-type generator. Kuiper–Lee, Appointment Scheduling for
Multiple Servers, SSRN 3975471, Eqs. (8), (13), pp.12-13 and Eq. (15), p.14.

**Formalization Note** The statement concerns matrices only, so its hypotheses are those of
`IsDPHSModel` on `α`, `S`, `s` and `x`. -/
theorem phase_type_representation {ι : Type*} [Fintype ι] [DecidableEq ι] (s m : ℕ) (α : ι → ℝ)
    (S : Matrix ι ι ℝ) (x : ℕ → ℝ) (hs : 1 ≤ s) (hrep : MatrixAnalytic.PH.IsPHRep α S)
    (hsum : ∑ a, α a = 1) (hdet : IsUnit S.det)
    (hx : ∀ l ∈ Finset.Icc 1 m, 0 ≤ x (s + l)) (i : ℕ) (hi : i ≤ m) :
    MatrixAnalytic.PH.IsPHRep (alphaSys α S s x i) (sysMat α S s i) ∧
    ∑ p, alphaSys α S s x i p = 1 ∧
    IsUnit (sysMat α S s i).det := by sorry

end MultiServerAppt
