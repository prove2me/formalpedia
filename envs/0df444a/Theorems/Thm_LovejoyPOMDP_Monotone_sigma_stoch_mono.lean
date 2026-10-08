-- Prove2me | Theorems.Thm_LovejoyPOMDP_Monotone_sigma_stoch_mono
-- name    : LovejoyPOMDP.Monotone.sigma_stoch_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:56:59.88483+00:00
-- url     : https://prove2.me/theorems/cf733483-dc14-47e8-b087-a2063bb62713
-- title:
--   Proof of Proposition 1, p. 739 — under (c), (d), π ≥r π′ implies σ(π, a) ≥s σ(π′, a)
-- statement:
--   Consider a finite POMDP as in §2 of the paper. Assume
--
--   1. (c) each transition matrix $P^a$ is $\mathrm{TP}_2$, and
--   2. (d) $r^a(j)\ge_r r^a(j')$ for all $j\ge j'$ in $S$ and all $a\in A$.
--
--   Then for all beliefs $\pi,\pi'\in\Pi(S)$ with $\pi\ge_r\pi'$ and every action $a\in A$, the observation distributions are stochastically ordered:
--   $$\sigma(\pi,a)\ \ge_s\ \sigma(\pi',a),$$
--   that is, $\sum_{k\ge q}\sigma(k;\pi,a)\ge\sum_{k\ge q}\sigma(k;\pi',a)$ for every $q\in O$.
--
--   A higher belief makes higher observations more likely. This is the first step of the induction in the proof of Proposition 1.
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 739, §4, proof of Proposition 1 (unnumbered: "Consequently, π ≥r π′ implies σ(π, a) ≥s σ(π′, a) for any a ∈ A")

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Model

namespace LovejoyPOMDP.Monotone

/-- Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, §4, proof of Proposition 1, p. 739 (unnumbered): "Consequently, `π ≥r π'` implies
`σ(π, a) ≥s σ(π', a)` for any `a ∈ A`."

Under assumptions (c) and (d) of Proposition 1 — every `P^a` is TP₂, and `r^a(j) ≥r r^a(j')` for
`j ≥ j'` in `S`, `a ∈ A` — if `π ≥r π'` in `Π(S)` then `σ(π, a) ≥s σ(π', a)` (as vectors over `O`)
for every `a ∈ A`. -/
theorem sigma_stoch_mono {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    (hP : ∀ a, TP2 (M.P a))
    (hR : ∀ a (j j' : S), j' ≤ j → MLRGE (M.R a j) (M.R a j'))
    {π π' : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (hπ' : π' ∈ stdSimplex ℝ S) (h : MLRGE π π')
    (a : A) :
    StochGE (M.sigma π a) (M.sigma π' a) := by sorry

end LovejoyPOMDP.Monotone
