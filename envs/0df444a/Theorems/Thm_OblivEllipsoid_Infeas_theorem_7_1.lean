-- Prove2me | Theorems.Thm_OblivEllipsoid_Infeas_theorem_7_1
-- name    : OblivEllipsoid.Infeas.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:41.692094+00:00
-- url     : https://prove2.me/theorems/a0643243-b026-40a1-8639-0f6d16785ae9
-- title:
--   Theorem 7.1 — OEA returns an infeasibility certificate within the stated bound
-- statement:
--   Suppose the columns of $A$ conically span $\mathbb R^n$ and have unit Euclidean norm. Start Algorithm 4 with $d=e$ and any certified lower bounds $(\ell,\Lambda)$. If $A^\top x\le u$ is infeasible, every admissible run can continue from each reached state, returns only a type-L certificate satisfying $A\lambda=0$, $\lambda\ge0$, and $u^\top\lambda<0$, and has at most
--   $$\left\lfloor2m(m+1)\ln\left(\frac{m+1}{2m}\frac{\|u-\ell\|_2}{\tau(A,u)}\right)\right\rfloor$$
--   completed updates before termination.
--
--   The statement quantifies over all the index and step-size choices left open by Procedures 2–3 and Algorithm 4. It supplies a finite iteration guarantee and an explicit infeasibility witness.
--
--   **Formalization Note** A completed update is a pass reaching Step 12; the stopping pass follows it. The bound is asserted for states after $k\ge1$ completed updates, as in the proof on page 22. A first-pass stop can have a negative displayed logarithmic bound, so $k=0$ is excluded. The Euclidean norm is written as a square-root of the sum of squares.
-- source:
--   Lamperski, Freund & Todd, An Oblivious Ellipsoid Algorithm for Solving a System of (In)Feasible Linear Inequalities, arXiv:1910.03114v5, p. 22, Theorem 7.1

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas

/-- Theorem 7.1, p. 22, on all admissible runs of Algorithm 4. -/
theorem theorem_7_1 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u : Fin m → ℝ) (hA : Assumption11 A)
    (ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hcert : CertLB A u ell Lam)
    (hinf : ¬ ∃ x : Fin n → ℝ, IsFeasible A u x) :
    let s0 : State m := ⟨fun _ => 1, ell, Lam⟩
    (∀ k s, Reach A u s0 k s → ∃ o, OEAIter A u s o) ∧
    (∀ k s lam, Reach A u s0 k s →
      OEAIter A u s (.certificate lam) → IsAlt A u lam) ∧
    (∀ k s x, Reach A u s0 k s → ¬ OEAIter A u s (.solution x)) ∧
    (∀ k s, Reach A u s0 k s → 1 ≤ k →
      (k : ℤ) ≤ ⌊2 * (m : ℝ) * ((m : ℝ) + 1) *
        Real.log (((m : ℝ) + 1) / (2 * (m : ℝ)) *
          Real.sqrt (∑ i : Fin m, (u i - ell i) ^ 2) / tau A u)⌋) := by sorry

end OblivEllipsoid.Infeas
