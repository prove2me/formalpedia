-- Prove2me | Theorems.Thm_LovejoyPOMDP_Monotone_mlr_implies_stoch
-- name    : LovejoyPOMDP.Monotone.mlr_implies_stoch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:39:20.39534+00:00
-- url     : https://prove2.me/theorems/39535bcd-7faf-47cc-bf3e-68d8e2042ce4
-- title:
--   §1, p. 737 — the MLR order implies first-order stochastic dominance on Π(X)
-- statement:
--   Let $X$ be a finite chain and let $\pi,\pi'\in\Pi(X)$ be probability vectors on $X$. If $\pi$ dominates $\pi'$ in the monotone likelihood ratio order, then it dominates $\pi'$ stochastically:
--   $$\pi\ge_r\pi'\ \Longrightarrow\ \pi\ge_s\pi'.$$
--
--   This is the sense in which the MLR order is stronger than first-order stochastic dominance; it lets every MLR-monotonicity result be converted into a statement about expectations of nondecreasing functions.
--
--   **Formalization Note** Both vectors must be probability vectors: the implication fails for unnormalized vectors.
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 737, §1 (unnumbered, after Lemma 1.1)

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Orders

namespace LovejoyPOMDP.Monotone

/-- Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, §1, p. 737 (unnumbered): "`≤r` … is stronger than `≤s` in that `π' ≤r π`
implies `π' ≤s π`."

For probability vectors `π, π' ∈ Π(X)` on a finite chain `X`, `π ≥r π'` implies `π ≥s π'`.

**Formalization Note.** Both vectors are assumed to lie in the simplex, as in the paper; the
implication fails for unnormalized vectors. -/
theorem mlr_implies_stoch {X : Type*} [Fintype X] [LinearOrder X] {π π' : X → ℝ}
    (hπ : π ∈ stdSimplex ℝ X) (hπ' : π' ∈ stdSimplex ℝ X) (h : MLRGE π π') :
    StochGE π π' := by sorry

end LovejoyPOMDP.Monotone
