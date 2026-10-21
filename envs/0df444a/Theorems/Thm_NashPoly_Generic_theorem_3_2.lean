-- Prove2me | Theorems.Thm_NashPoly_Generic_theorem_3_2
-- name    : NashPoly.Generic.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:51.4408+00:00
-- url     : https://prove2.me/theorems/517aefa5-05e1-4224-af08-3e494ee9a97a
-- title:
--   Theorem 3.2 (corrected), p. 10 — finite loop bound and terminal extension when (3.8) attains minima
-- statement:
--   Let a NEPP be given with polynomial multiplier expressions: matrix polynomials $H_i(x_i)$ with $H_i(x_i)G_i(x_i)=I_{m_i}$ for every player $i$, and $\lambda_{i,j}(x)=(H_i(x_i)\hat f_i(x))_j$ as in (3.3). Let $\Theta$ be positive definite, $G$ the feasible set of (3.7) and $G^*$ the set of all Nash equilibria. If $G\setminus G^*$ is finite, with $\ell^*=|G\setminus G^*|$, then every run of Algorithm 3.1 completes at most $\ell^*$ loops:
--   $$L\le \ell^*=|G\setminus G^*|$$
--   for every run that has completed $L$ executions of Step 3.
--
--   If every player test (3.8) attains a minimum at every point of $G$, then every partial run extends, preserving its candidates and cut sets, to a terminal run with at most $\ell^*$ loops. Its last Step 1 either finds (3.10) infeasible or produces a minimizing Nash equilibrium. This attainment condition makes explicit the qualification needed for the paper's claim of an actual answer.
--
--   **Formalization Note** A run is any sequence of choices the algorithm permits (see the definition of runs), so the bound holds for every way of choosing the optimizers. The loop count $L$ is the paper's counter $\ell$.
-- source:
--   Nie & Tang, Nash Equilibrium Problems of Polynomials, arXiv:2006.09490v2, p. 10, Theorem 3.2

import Mathlib
import Definitions.Def_NashPoly_Generic_Algorithm

namespace NashPoly.Generic

open MvPolynomial Matrix

/-- Theorem 3.2, p. 10, corrected for the possible nonattainment of (3.8): with polynomial
multiplier expressions and `G \ G*` finite, every run completes at most `|G \ G*|` loops.
If the player tests (3.8) attain minima at all candidates, every partial run extends to a
terminal run within that bound; its final call either detects infeasibility or finds an NE. -/
theorem theorem_3_2 {N : ℕ} {n m : Fin N → ℕ} (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (hH : ∀ i, H i * Gmat (P.g i) = 1)
    (Θ : Matrix (Option (Var n)) (Option (Var n)) ℝ) (hΘ : Θ.PosDef)
    (hfin : (P.GSet H \ P.NESet).Finite) :
    (∀ (L : ℕ) (K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
        (u : Fin L → Var n → ℝ),
      P.IsRun H Θ L K u → L ≤ (P.GSet H \ P.NESet).ncard) ∧
    (P.Step38Solvable H →
      ∀ (L : ℕ) (K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
        (u : Fin L → Var n → ℝ), P.IsRun H Θ L K u →
        ∃ (L' : ℕ) (K' : Fin (L' + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
          (u' : Fin L' → Var n → ℝ) (h : L ≤ L'),
          P.RunExtends h K u K' u' ∧ P.IsRun H Θ L' K' u' ∧
            L' ≤ (P.GSet H \ P.NESet).ncard ∧
            P.IsTerminal H Θ (K' (Fin.last L'))) := by sorry

end NashPoly.Generic
