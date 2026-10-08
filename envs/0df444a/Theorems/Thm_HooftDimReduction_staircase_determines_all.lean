-- Prove2me | Theorems.Thm_HooftDimReduction_staircase_determines_all
-- name    : HooftDimReduction.staircase_determines_all
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T01:23:58.263893+00:00
-- url     : https://prove2.me/theorems/b0c68f5a-65a1-41c2-8f2e-55adf8f8c463
-- title:
--   Goal: in the plaquette automaton on $\mathbb Z^3$, the data on the staircase (14) determine all data
-- statement:
--   Let $p\in\mathbb N$. On every plaquette $(x,P)$ of the cubic lattice $\mathbb Z^3$ (corners $x,\,x+u,\,x+u+v,\,x+v$ in cyclic order) impose a relation $g_{x,P}(f_1,f_2,f_3,f_4)=0$ with values in $\mathbb Z/p$ such that, whenever three of the four entries are given, the fourth is uniquely determined (eq. (12) and the sentence after it). The relations may vary from plaquette to plaquette. Let $x(n)$, $n\in\mathbb Z$, be the staircase of eq. (14) starting at $x_0$. If $f,f':\mathbb Z^3\to\mathbb Z/p$ both satisfy all plaquette relations and
--   $$f(x(n))=f'(x(n))\quad\text{for all }n\in\mathbb Z,$$
--   then $f=f'$ on all of $\mathbb Z^3$.
--
--   This is the dimensional-reduction property of 't Hooft's cellular automaton: data on a one-dimensional line fix the state of the whole $2+1$-dimensional space-time lattice.
--
--   **Formalization Note** "Fixes all data elsewhere" is formalized as uniqueness: two solutions agreeing on the staircase coincide. No consistency (16) is assumed; it is only needed for existence of solutions.
-- source:
--   G. 't Hooft, "Dimensional Reduction in Quantum Gravity", essay dedicated to Abdus Salam, Utrecht preprint THU-93/26, arXiv:gr-qc/9310026v2, https://arxiv.org/abs/gr-qc/9310026, pp. 8–10, Fig. 1, eqs. (12a–f), (14): 'Suppose f(x(n)) are given for all n. Successive application of the six identities (12a–f) then also fixes all data elsewhere.'

import Mathlib
import Definitions.Def_HooftDimReduction_Defs

namespace HooftDimReduction

theorem staircase_determines_all (p : ℕ) (g : Site → Plane → (Fin 4 → ZMod p) → ZMod p)
    (hg : ∀ x P, IsPlaquetteRule (g x P)) (x₀ : Site) (f f' : Site → ZMod p)
    (hf : SatisfiesRules g f) (hf' : SatisfiesRules g f')
    (hstair : ∀ n : ℤ, f (staircase x₀ n) = f' (staircase x₀ n)) :
    f = f' := by sorry

end HooftDimReduction
