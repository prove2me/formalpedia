-- Prove2me | Theorems.Thm_NashPoly_Generic_theorem_3_3
-- name    : NashPoly.Generic.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:47.996322+00:00
-- url     : https://prove2.me/theorems/28ecd47d-845a-4ec7-8d88-3cc17ad1fb33
-- title:
--   Theorem 3.3 (corrected), p. 10 — generic finite loop bound and conditional termination with a correct answer
-- statement:
--   Fix positive degrees $a_{i,j}>0$ ($i,j\in[N]$; the degree of $f_i$ in $x_j$) and $d_{i,j}>0$ ($i\in[N]$, $j\in[m_i]$; the degree of $g_{i,j}$ in $x_i$). For Lebesgue-almost every coefficient vector $c$ of the input data, the following holds for every choice of equality labels $E_i$, every family of matrix polynomials $H_i(x_i)$ with $H_i(x_i)G_i(x_i)=I_{m_i}$ (the polynomial multiplier expressions (3.3)), and every positive definite $\Theta\in\mathbb R^{(n+1)\times(n+1)}$:
--
--   1. **Finite termination.** There is $L^*\in\mathbb N$ such that every run of Algorithm 3.1 completes at most $L^*$ loops.
--   2. **Correct stops.** For every run, with final cut sets $K$:
--      - if (3.10) is infeasible, the NEPP has no Nash equilibrium;
--      - if (3.10) is feasible, it has a minimizer of $[x]_1^T\Theta[x]_1$, so Step 1 produces a candidate.
--   3. **Terminal extension.** If every player test (3.8) attains a minimum at every candidate in $G$, every partial run extends to a terminal run within the same finite loop bound. That terminal run either finds an NE or correctly detects that none exists.
--
--   The output "NE $u$" of Step 2 is a Nash equilibrium by definition of the test. The unconditional bound is:
--   $$\exists L^*\ \forall\text{ runs with } L \text{ loops}:\ L\le L^* .$$
--
--   This is a corrected version of the paper's main guarantee. The paper observes that (3.8) may not attain a minimum on an unbounded strategy set; its unconditional answer claim needs the explicit attainment condition in clause 3. The loop bound and stopping rule correctness need no such condition.
--
--   **Formalization Note** "Generic" is "for all coefficient vectors outside a Lebesgue-null set" of the space of polynomials with the given degree bounds; the null set depends only on the degrees, not on $E$, $H$ or $\Theta$. A run is any sequence of choices permitted by Algorithm 3.1 (which optimizer of (3.10), which optimizers of (3.8)). `Step38Solvable` is the attainment condition in clause 3. If no $H$ with $H_iG_i=I$ exists the statement is vacuous for that $c$; the paper cites [42, 44] for their existence under nonsingularity.
-- source:
--   Nie & Tang, Nash Equilibrium Problems of Polynomials, arXiv:2006.09490v2, p. 10, Theorem 3.3 (proof: Theorems 3.2 and A.1)

import Mathlib
import Definitions.Def_NashPoly_Generic_Algorithm
import Definitions.Def_NashPoly_Generic_Coef

namespace NashPoly.Generic

open MvPolynomial Matrix MeasureTheory

/-- Theorem 3.3, p. 10, corrected for the possible nonattainment of (3.8):
for positive degrees `a_{i,j}` (degree of `f_i` in `x_j`) and `d_{i,j}`
(degree of `g_{i,j}` in `x_i`), for Lebesgue-almost every coefficient vector, whatever the
equality labels `E_i`, the polynomial multiplier expressions `H_i` (`H_i G_i = I`) and the
positive definite `Θ`:
(a) there is a bound `L` on the number of loops of every run of Algorithm 3.1;
(b) at the end of every run, if (3.10) is infeasible there is no Nash equilibrium, and if it is
feasible it has a minimizer;
(c) if every (3.8) test attains a minimum, every partial run extends to a terminal run within
the bound, ending with a Nash equilibrium or a correct infeasibility report. -/
theorem theorem_3_3 {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j) (hd : ∀ i j, 0 < d i j) :
    ∀ᵐ c ∂(volume : Measure (Coef n m a d)),
      ∀ (E : (i : Fin N) → Finset (Fin (m i)))
        (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ)),
      (∀ i, H i * Gmat ((nepOf c E).g i) = 1) →
      ∀ Θ : Matrix (Option (Var n)) (Option (Var n)) ℝ, Θ.PosDef →
        (∃ B : ℕ,
          (∀ (L : ℕ) (K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
            (u : Fin L → Var n → ℝ), (nepOf c E).IsRun H Θ L K u → L ≤ B) ∧
          ((nepOf c E).Step38Solvable H →
            ∀ (L : ℕ) (K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
              (u : Fin L → Var n → ℝ), (nepOf c E).IsRun H Θ L K u →
              ∃ (L' : ℕ) (K' : Fin (L' + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
                (u' : Fin L' → Var n → ℝ) (h : L ≤ L'),
                (nepOf c E).RunExtends h K u K' u' ∧
                  (nepOf c E).IsRun H Θ L' K' u' ∧ L' ≤ B ∧
                  (nepOf c E).IsTerminal H Θ (K' (Fin.last L')))) ∧
        ∀ (L : ℕ) (K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
          (u : Fin L → Var n → ℝ), (nepOf c E).IsRun H Θ L K u →
          ((nepOf c E).Feas H (K (Fin.last L)) = ∅ → (nepOf c E).NESet = ∅) ∧
          (((nepOf c E).Feas H (K (Fin.last L))).Nonempty →
            ∃ x ∈ (nepOf c E).Feas H (K (Fin.last L)),
              IsMinOn (theta Θ) ((nepOf c E).Feas H (K (Fin.last L))) x) := by sorry

end NashPoly.Generic
