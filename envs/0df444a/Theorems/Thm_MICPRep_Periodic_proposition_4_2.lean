-- Prove2me | Theorems.Thm_MICPRep_Periodic_proposition_4_2
-- name    : MICPRep.Periodic.proposition_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:10.056865+00:00
-- url     : https://prove2.me/theorems/3611bd2e-0df9-4771-a3b2-4504ffd13f52
-- title:
--   Proposition 4.2, pp. 10–11 — binary MICP-R sets are exactly finite unions of projections of nonempty closed convex sets, via the lifted formulation (4.4)
-- statement:
--   Let $S \subseteq \mathbb R^n$. Then $S$ is binary MICP-R if and only if there are $q \in \mathbb Z_+$, $k \in \mathbb Z_+$ and nonempty closed convex sets $\tilde S_1, \dots, \tilde S_k \subseteq \mathbb R^{n+q}$ such that
--   $$S = \bigcup_{i=1}^k \mathrm{proj}_x(\tilde S_i).$$
--   Moreover, for any such sets the closed convex set
--   $$M = \mathrm{conv}\Bigl(\bigcup_{i=1}^k T_i \times \{e(k,i)\}\Bigr) \subseteq \mathbb R^{n+(q+1)+k}, \qquad T_i = \{(w, w_0) : w \in \tilde S_i,\ \|w\|_2^2 \le w_0\},$$
--   induces an MICP formulation of $S$ (with $p = q+1$ continuous variables) and every point of $M$ with integer $z$ has $z \in \{0,1\}^k$, so the formulation is binary.
--
--   The proposition removes the equal-recession-cone restriction of Jeroslow's characterization by one continuous lifting variable; it is how the main theorem's proof rewrites the binary part of its decomposition as a finite union of convex sets.
--
--   **Formalization Note** The number of sets $k$ is existential and is unrelated to the number of integer variables of a given binary formulation of $S$; in (4.4) the formulation built has exactly $k$ integer variables. The squared norm of $w = (x, y')$ is $\|x\|_2^2 + \sum_j y_j'^2$. The set $M$ is the module `liftedHull`.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, pp. 10–11, Proposition 4.2 and formulation (4.4)

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- Proposition 4.2, pp. 10–11. -/
theorem proposition_4_2 {n : ℕ} (S : Set (Pt n)) :
    (IsBinaryMICPR S ↔
      ∃ (q k : ℕ) (St : Fin k → Set (Pt n × (Fin q → ℝ))),
        (∀ i, (St i).Nonempty ∧ IsClosed (St i) ∧ Convex ℝ (St i)) ∧
        S = ⋃ i, Prod.fst '' St i) ∧
    ∀ (q k : ℕ) (St : Fin k → Set (Pt n × (Fin q → ℝ))),
      (∀ i, (St i).Nonempty ∧ IsClosed (St i) ∧ Convex ℝ (St i)) →
      S = ⋃ i, Prod.fst '' St i →
      Induces (liftedHull St) S ∧
        ∀ v ∈ liftedHull St, v.2.2 ∈ intLattice k → ∀ i : Fin k, v.2.2 i = 0 ∨ v.2.2 i = 1 := by sorry

end MICPRep.Periodic
