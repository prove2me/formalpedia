-- Prove2me | Theorems.Thm_LawlerWCT_RhoMax_max_weight_initial_set_rhoMaximal
-- name    : LawlerWCT.RhoMax.max_weight_initial_set_rhoMaximal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:09.067292+00:00
-- url     : https://prove2.me/theorems/54d7793a-1186-42d1-a849-825d6197f9c8
-- title:
--   §7, pp. 16–17 — at the smallest point of an interval of length 1/(np*)² containing the optimal ratio, a maximum-weight initial set is ρ-maximal
-- statement:
--   Let $G=(N,A)$ be an acyclic digraph on a finite set $N$ of $n=|N|$ jobs, where job $i$ must precede job $j$ when $G$ has a directed path from $i$ to $j$. Let the weights and processing times be integers with
--   $$-w^*\le w_j\le w^*,\qquad 1\le p_j\le p^*\qquad(j\in N),$$
--   and let $\rho^*=\rho(I^*)$ be the optimal ratio, the ratio of a ρ-maximal initial set $I^*$ of $N$. Let $\rho$ be a real number with
--   $$\rho\le\rho^*\le\rho+\varepsilon,\qquad\varepsilon=\frac{1}{(n\,p^*)^2},$$
--   i.e. the smallest value of an interval of length $\varepsilon$ known to contain the optimal ratio. Let $I$ be a nonempty initial set of $N$ of maximum weight with respect to $\bar w_j=w_j-\rho p_j$ among all initial sets of $N$:
--   $$\sum_{j\in I'}(w_j-\rho p_j)\le\sum_{j\in I}(w_j-\rho p_j)\qquad\text{for every initial set } I' \text{ of } N .$$
--   Then $I$ is a ρ-maximal initial set of $N$.
--
--   This is the correctness of the last step of Lawler's binary search for a ρ-maximal initial set: after the search has narrowed the optimal ratio to an interval of length $\varepsilon$, one maximum-weight initial set computation (a minimum cut) at the left end of the interval returns a ρ-maximal initial set, which is what Sidney's decomposition of the sequencing problem requires.
--
--   **Formalization Note.** The maximum is over all initial sets, the empty one included, as a minimum cut delivers it. The hypothesis that $I$ is nonempty is added: when $\rho=\rho^*$ the empty set is a maximizer of trial weight $0$ but is not ρ-maximal, so the paper's sentence needs $I\neq\emptyset$; when $\rho<\rho^*$ every maximizer is nonempty anyway. The optimal ratio is given through a ρ-maximal initial set $I^*$; integer data are cast to reals, and $n$ and $p^*$ are cast to reals before dividing. The closed interval $\rho\le\rho^*\le\rho+\varepsilon$ is the paper's "interval of length not exceeding $\varepsilon$" with $\rho$ its smallest value.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, pp. 16–17, §7, paragraph "It is sufficient to carry out a binary search ... In either case, the maximum weight initial set I which is determined is ρ-maximal."

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model

namespace LawlerWCT.RhoMax

theorem max_weight_initial_set_rhoMaximal {ι : Type*} [DecidableEq ι] (N : Finset ι)
    (G : ι → ι → Prop) (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N)
    (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (w p : ι → ℤ) (wstar pstar : ℤ)
    (hw : ∀ j ∈ N, -wstar ≤ w j ∧ w j ≤ wstar) (hpb : ∀ j ∈ N, 1 ≤ p j ∧ p j ≤ pstar)
    (Istar : Finset ι)
    (hIstar : LawlerWCT.SeriesPar.IsRhoMaximal G (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) N Istar)
    (ρ : ℝ)
    (hlo : ρ ≤ LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) Istar)
    (hhi : LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) Istar ≤
      ρ + 1 / ((N.card : ℝ) * (pstar : ℝ)) ^ 2) :
    ∀ I, LawlerWCT.SeriesPar.IsInitialSet G N I → I.Nonempty →
      (∀ I', LawlerWCT.SeriesPar.IsInitialSet G N I' →
        trialWeight (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) ρ I' ≤
          trialWeight (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) ρ I) →
      LawlerWCT.SeriesPar.IsRhoMaximal G (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) N I := by sorry

end LawlerWCT.RhoMax
