-- Prove2me | Theorems.Thm_NashBargainingProblem_Axiomatic_nash_axioms_force_nash_product_max
-- name    : NashBargainingProblem.Axiomatic.nash_axioms_force_nash_product_max
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:20:53.859152+00:00
-- url     : https://prove2.me/theorems/fc34f4c5-a9ce-460f-a7b7-223c59a12968
-- title:
--   p. 159 — a solution satisfying selection, INV, SYM, IIA and PAR picks the maximizer of the Nash product
-- statement:
--   A **bargaining problem** is a pair $\langle S,d\rangle$ with $S\subseteq\mathbb R^2$ compact and convex, $d\in S$ the disagreement point, and some $s\in S$ with $s_1>d_1$ and $s_2>d_2$; let $\mathcal B$ be the set of them. Let $g$ assign to each $\langle S,d\rangle\in\mathcal B$ a point $g(S,d)\in\mathbb R^2$ and assume:
--
--   1. (selection) $g(S,d)\in S$;
--   2. (INV) for $\alpha_1,\alpha_2>0$, $\beta_1,\beta_2\in\mathbb R$ and $L(s)=(\alpha_1s_1+\beta_1,\ \alpha_2s_2+\beta_2)$: if $\langle L(S),L(d)\rangle\in\mathcal B$ then $g(L(S),L(d))=L(g(S,d))$;
--   3. (SYM, Nash's assumption 8) if $d_1=d_2$ and $(s_1,s_2)\in S\iff(s_2,s_1)\in S$, then $g(S,d)_1=g(S,d)_2$;
--   4. (IIA, Nash's assumption 7) if $S\subseteq T$, both $\langle S,d\rangle,\langle T,d\rangle\in\mathcal B$, and $g(T,d)\in S$, then $g(S,d)=g(T,d)$;
--   5. (PAR, Nash's assumption 6) if $s,t\in S$ with $t_1>s_1$ and $t_2>s_2$, then $g(S,d)\ne s$.
--
--   Then for every $\langle S,d\rangle\in\mathcal B$, writing $p=g(S,d)$: $p_1\ge d_1$, $p_2\ge d_2$, and
--
--   $$
--   \forall s\in S,\quad s_1\ge d_1,\ s_2\ge d_2,\ s\ne p\ \Longrightarrow\ (s_1-d_1)(s_2-d_2)<(p_1-d_1)(p_2-d_2).
--   $$
--
--   That is, the solution is the point of the set in the first quadrant (relative to $d$) where the product of the utility gains is maximized. This is the assertion Nash proves on p. 159, the necessity half of his characterization.
--
--   **Formalization Note** The five hypotheses are copied verbatim from the left-hand side of the Open platform theorem `NashBargaining.nash_bargaining_solution_unique`, and the conclusion is its last conjunct with $g$ in place of $f$, so this milestone is the "only if" direction of that goal. The paper fixes $d$ at the origin by the normalization of p. 158 ("assign the number zero to this anticipation"); the translation by $-d$, i.e. INV with $\beta=-d$, is that normalization. The paper's INV is implicit: utilities are determined only up to positive scale (p. 158), and its assumption 8 allows symmetry after a rescaling, which with INV is the literal SYM above.
-- source:
--   Nash, The Bargaining Problem, Econometrica 18 (1950), p. 159, Two Person Theory, assumptions 6–8 and the proof of the assertion ("We now show that these conditions require that the solution be the point of the set in the first quadrant where u1 u2 is maximized. … Now using assumption (7) we may conclude that (1, 1) must also be the solution point when our original (transformed) set is the set of alternatives. This establishes the assertion."); normalization p. 158

import Mathlib

namespace NashBargainingProblem.Axiomatic
theorem nash_axioms_force_nash_product_max
    (B : Set (Set (ℝ × ℝ) × (ℝ × ℝ)))
    (hB : B = {P | IsCompact P.1 ∧ Convex ℝ P.1 ∧ P.2 ∈ P.1 ∧
      ∃ s ∈ P.1, P.2.1 < s.1 ∧ P.2.2 < s.2})
    (g : B → ℝ × ℝ)
    -- g is a bargaining solution: it selects a point of S
    (h_sel : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), g ⟨(S, d), h⟩ ∈ S)
    -- INV: invariance under positive affine rescalings of the two utilities
    (h_inv : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B)
            (α₁ α₂ β₁ β₂ : ℝ) (L : ℝ × ℝ → ℝ × ℝ), 0 < α₁ → 0 < α₂ →
            (∀ s : ℝ × ℝ, L s = (α₁ * s.1 + β₁, α₂ * s.2 + β₂)) →
            ∀ h' : (L '' S, L d) ∈ B, g ⟨(L '' S, L d), h'⟩ = L (g ⟨(S, d), h⟩))
    -- SYM: symmetric problems get symmetric outcomes
    (h_sym : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), d.1 = d.2 →
            (∀ s₁ s₂ : ℝ, (s₁, s₂) ∈ S ↔ (s₂, s₁) ∈ S) →
            (g ⟨(S, d), h⟩).1 = (g ⟨(S, d), h⟩).2)
    -- IIA: independence of irrelevant alternatives
    (h_iia : ∀ (S T : Set (ℝ × ℝ)) (d : ℝ × ℝ) (hS : (S, d) ∈ B) (hT : (T, d) ∈ B),
            S ⊆ T → g ⟨(T, d), hT⟩ ∈ S → g ⟨(S, d), hS⟩ = g ⟨(T, d), hT⟩)
    -- PAR: Pareto efficiency (a point of S strictly improved upon by some t ∈ S is never chosen)
    (h_par : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), ∀ s ∈ S, ∀ t ∈ S,
            s.1 < t.1 → s.2 < t.2 → g ⟨(S, d), h⟩ ≠ s) :
    ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B),
      d.1 ≤ (g ⟨(S, d), h⟩).1 ∧ d.2 ≤ (g ⟨(S, d), h⟩).2 ∧
      ∀ s ∈ S, d.1 ≤ s.1 → d.2 ≤ s.2 → s ≠ g ⟨(S, d), h⟩ →
        (s.1 - d.1) * (s.2 - d.2) <
          ((g ⟨(S, d), h⟩).1 - d.1) * ((g ⟨(S, d), h⟩).2 - d.2) := by sorry
end NashBargainingProblem.Axiomatic
