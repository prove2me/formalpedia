-- Prove2me | Theorems.Thm_HooftDimReduction_altRule_staircase_extension
-- name    : HooftDimReduction.altRule_staircase_extension
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T01:23:27.256534+00:00
-- url     : https://prove2.me/theorems/ed33f9d2-d1c0-4355-b9b6-b22f2a5a295b
-- title:
--   Eqs. (14) & (17): for the linear rule $f_1-f_2+f_3-f_4\equiv0$, staircase data extend uniquely to all of $\mathbb Z^3$
-- statement:
--   Let $p\in\mathbb N$, $x_0\in\mathbb Z^3$, and let $\varphi:\mathbb Z\to\mathbb Z/p$ be arbitrary data on the staircase $x(n)$ of eq. (14) starting at $x(0)=x_0$. Impose on **every** plaquette of $\mathbb Z^3$, with corners in cyclic order, the linear relation
--   $$f_1-f_2+f_3-f_4\equiv 0\pmod p .$$
--   Then there is exactly one $f:\mathbb Z^3\to\mathbb Z/p$ that satisfies all these relations and takes the prescribed values $f(x(n))=\varphi(n)$ for all $n\in\mathbb Z$.
--
--   So for this consistent linear model the staircase data are free, and they determine everything: the lattice degrees of freedom are exactly those of the one-dimensional staircase (dimensional reduction).
--
--   **Formalization Note** The essay states the determination claim for general relations and discusses linear relations in eq. (17). This statement is the linear special case with a specific choice of signs, including the existence half.
-- source:
--   G. 't Hooft, "Dimensional Reduction in Quantum Gravity", essay dedicated to Abdus Salam, Utrecht preprint THU-93/26, arXiv:gr-qc/9310026v2, https://arxiv.org/abs/gr-qc/9310026, pp. 9–11: eq. (14) and 'Suppose f(x(n)) are given for all n. Successive application of the six identities (12a–f) then also fixes all data elsewhere', combined with the linear rules of eq. (17)

import Mathlib
import Definitions.Def_HooftDimReduction_Defs

namespace HooftDimReduction

theorem altRule_staircase_extension (p : ℕ) (x₀ : Site) (φ : ℤ → ZMod p) :
    ∃! f : Site → ZMod p,
      SatisfiesRules (fun _ _ => altRule) f ∧ ∀ n : ℤ, f (staircase x₀ n) = φ n := by sorry

end HooftDimReduction
