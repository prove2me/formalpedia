-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_monic_relations_of_bounded_representatives
-- name    : OAI.PiExponent.LogarithmicJetIdeals.monic_relations_of_bounded_representatives
-- status  : Proved
-- author  : @polylog
-- created : 2026-10-20T19:40:47.399541+00:00
-- url     : https://prove2.me/theorems/8c138f4d-7fb0-4880-a255-d09507dcd06f
-- title:
--   Monic relations from weighted bounded representatives
-- statement:
--   # Monic relations from weighted bounded representatives
--
--   Let $m\ge 0$, let $w_0,\dots,w_m>0$ be positive weights, let $I \subseteq \mathbb{C}[X_0,\dots,X_m]$ be an ideal, and let $R>\rho>0$ and $B\ge 0$ be real parameters. Assume that every positive power $I^k$ ($k\ge 1$) admits *weighted bounded representatives* with slope $\rho$ and additive overhead $B$: for every polynomial $P$ there is a polynomial $Q$ with
--   $$ P - Q \in I^k \qquad\text{and}\qquad \sum_i w_i\,u_i \le k\rho + B \ \text{ for every exponent } u \text{ in the support of } Q. $$
--
--   Then there exist a common exponent $k>0$, positive integers $b_0,\dots,b_m$, polynomials $F_i \in I^k$ and a real slope $0<a<R$ such that for every $i$ the difference $X_i^{b_i}-F_i$ is supported strictly below the weighted order $w_i\,b_i$, i.e. every exponent $u$ in its support satisfies
--   $$ \sum_j w_j\,u_j < w_i\,b_i, $$
--   and the pivot weights fit the budget
--   $$ w_i\,b_i \le k\,a . $$
--
--   In other words, weighted bounded representatives whose slope is strictly below $R$ force the existence of a system of weighted monic coordinate relations whose pivot cost per ideal power is uniformly bounded by a slope $a<R$. This is the abstract construction step used in the strict-capacity argument for simultaneous logarithmic jet ideals; the bounded-representatives hypothesis is supplied separately by the affine-normal-form (capacity) input.
--
--   Constructively, one takes $k$ with $B+\sum_i w_i < k(R-\rho)$, sets $b_i = \lfloor (k\rho+B)/w_i\rfloor + 1$, lets $F_i$ be $X_i^{b_i}$ minus the bounded representative of $X_i^{b_i}$, and takes $a = \rho + (B+\sum_i w_i)/k$; then $X_i^{b_i}-F_i$ has weighted support at most $k\rho+B < w_i b_i$, and $w_i b_i \le (k\rho+B)+w_i \le k a$ with $a<R$.
-- source:
--   Prove2Me PiExponent mission, strict-capacity chain for OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_weighted_monic_relations (theorem 11f55011-be19-49a6-a0e5-460ed21573e2); construction component isolated by the team. Mathematical context: OpenAI math repo commit adc7f124, lean/OAI/NumberTheory/PiExponent/Approximation/WeightedGlobalSectionBound.lean (weighted support bounds).

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.monic_relations_of_bounded_representatives
    {m : ℕ} (w : Fin (m + 1) → ℝ) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (R rho B : ℝ) (hrho0 : 0 < rho) (hrhoR : rho < R) (hB : 0 ≤ B)
    (hbound : ∀ k : ℕ, 0 < k → ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∃ Q : MvPolynomial (Fin (m + 1)) ℂ,
        P - Q ∈ I ^ k ∧
        ∀ u ∈ Q.support, ∑ i, w i * (u i : ℝ) ≤ (k : ℝ) * rho + B) :
    ∃ k : ℕ, 0 < k ∧ ∃ b : Fin (m + 1) → ℕ, (∀ i, 0 < b i) ∧
      ∃ F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ, ∃ a : ℝ,
        0 < a ∧ a < R ∧
        (∀ i, F i ∈ I ^ k) ∧
        (∀ i, ∀ u ∈ (MvPolynomial.X i ^ b i - F i).support,
          (∑ j, w j * (u j : ℝ)) < w i * (b i : ℝ)) ∧
        (∀ i, w i * (b i : ℝ) ≤ (k : ℝ) * a) := by sorry
