-- Prove2me | Theorems.Thm_HooftDimReduction_exists_consistent_linear_rules
-- name    : HooftDimReduction.exists_consistent_linear_rules
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T01:20:59.614321+00:00
-- url     : https://prove2.me/theorems/d2449bbe-d5d8-4278-95ec-aa83632d5bed
-- title:
--   Eqs. (17)–(19): consistent linear plaquette relations with invertible coefficients exist mod $p$
-- statement:
--   For every modulus $p\ge 2$ there are coefficients $a_{k,j}\in\mathbb Z/p$ ($k=1,\dots,6$, $j=1,\dots,4$), all invertible modulo $p$, and constants $b_k\in\mathbb Z/p$, such that the six linear face relations (eq. (17))
--   $$g_k(f_1,f_2,f_3,f_4)=\sum_{j=1}^4 a_{k,j}f_j+b_k\equiv0\pmod p$$
--   on the faces (12a–f) of the unit cube are **consistent** (eq. (16)): for every choice of $f(A),f(B),f(D),f(E)$ there are values at the remaining corners $C,F,G,H$ that satisfy all six relations. Equivalently, the three values of $f(G)$ given by (15b), (15d), (15f) coincide, which is condition (19).
--
--   This shows that the commutation requirement for the two evolution laws can be met by linear rules.
--
--   **Formalization Note** Consistency is encoded as extendability of the four free values to data satisfying the six face relations of the unit cube at the origin.
-- source:
--   G. 't Hooft, "Dimensional Reduction in Quantum Gravity", essay dedicated to Abdus Salam, Utrecht preprint THU-93/26, arXiv:gr-qc/9310026v2, https://arxiv.org/abs/gr-qc/9310026, pp. 10–11, eqs. (15a–f), (16), (17)–(19): 'It is not hard to find sets of coefficients A_ij, B_i such that the 10 equations (19) are obeyed.'

import Mathlib
import Definitions.Def_HooftDimReduction_Defs

namespace HooftDimReduction

theorem exists_consistent_linear_rules (p : ℕ) (hp : 2 ≤ p) :
    ∃ (a : Fin 6 → Fin 4 → ZMod p) (b : Fin 6 → ZMod p),
      (∀ k j, IsUnit (a k j)) ∧ CubeConsistent (fun k => linearRule (a k) (b k)) := by sorry

end HooftDimReduction
