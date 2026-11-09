-- Prove2me | Theorems.Thm_GirthBethe_Sharp_bethe_variational_formula
-- name    : GirthBethe.Sharp.bethe_variational_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:20:54.534518+00:00
-- url     : https://prove2.me/theorems/5e7a9c6a-e421-4571-8ff6-1afed485110e
-- title:
--   Proposition 2.4 — variational formula for $\log\mathrm{Bethe}(A)$
-- statement:
--   Let $n\ge1$ and let $A\in\mathbb R^{n\times n}$ be nonnegative with $\mathrm{PM}(G_A)\neq\emptyset$. Then
--   $$\log\mathrm{Bethe}(A)=\max_{q\in\mathrm{PM}(G_A)}\Big\{\sum_{e\in E(G_A)}q_e\log A_e+H_B(q)\Big\},$$
--   the maximum being attained.
--
--   It converts the entropy inequality of Theorem 3.1 into a bound on the Bethe permanent.
--
--   Differences from the source:
--   - encoding: A ∈ ℝ^{n×n}_{≥0} with rows and columns indexed by [n] → A : Matrix (Fin n) (Fin n) ℝ with ∀ i j, 0 ≤ A i j (0-based indices); reason: relabelling only
--   - encoding: Bethe(A) := max over PM(G_A) in (1.1) → bethe A := sSup of the Bethe objective over PM(G_A) (0 if PM(G_A) = ∅), real powers with x^0 = 1; reason: the maximum is attained (item bethe_max_attained), so the supremum is the maximum; real powers give the boundary values 1 at p_e = 0 and A_e at p_e = 1, which are the limits by continuity
--   - encoding: log Bethe(A) = max_q {…} → IsGreatest of the set of values {∑_e q_e log A_e + H_B(q) : q ∈ PM(G_A)} at Real.log (bethe A); reason: IsGreatest says the value is attained and is the maximum
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 7, Proposition 2.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_BethePermanent

open Finset

namespace GirthBethe.Sharp

/-- Proposition 2.4: `log Bethe(A) = max_{q ∈ PM(G_A)} [∑_e q_e log A_e + H_B(q)]` when `PM(G_A) ≠ ∅`. -/
theorem bethe_variational_formula (n : ℕ) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hPM : (fracPM (supportEdges A)).Nonempty) :
    IsGreatest
      ((fun q => ∑ e : Edge (supportEdges A), q e * Real.log (A e.1.1 e.1.2) +
          betheEntropy (supportEdges A) q) '' fracPM (supportEdges A))
      (Real.log (bethe A)) := by sorry

end GirthBethe.Sharp
