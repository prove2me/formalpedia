-- Prove2me | Theorems.Thm_NashBargaining_nash_bargaining_solution_unique
-- name    : NashBargaining.nash_bargaining_solution_unique
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:29:51.407468+00:00
-- url     : https://prove2.me/theorems/66888fdf-8f87-4ad6-aba8-32a733724bb7
-- title:
--   Theorem 2.3 (Nash 1950): the Nash bargaining solution is the unique solution satisfying INV, SYM, IIA and PAR
-- statement:
--   This is Nash's axiomatic characterization of the two-player bargaining solution (Nash 1950), in the form of Theorem 2.3 of Osborne–Rubinstein, *Bargaining and Markets*.
--
--   A **bargaining problem** is a pair $\langle S,d\rangle$ in which $S\subseteq\mathbb{R}^2$ is compact and convex, $d=(d_1,d_2)\in S$ is the disagreement point, and there is some $s\in S$ with $s_1>d_1$ and $s_2>d_2$. Write $\mathcal{B}$ for the set of all bargaining problems. A **bargaining solution** is a function $f:\mathcal{B}\to\mathbb{R}^2$ such that $f(S,d)\in S$ for every $\langle S,d\rangle\in\mathcal{B}$. Consider the following four axioms on a bargaining solution $f$.
--
--   1. **INV (invariance to equivalent utility representations).** Let $\alpha_1,\alpha_2>0$ and $\beta_1,\beta_2\in\mathbb{R}$, and let $L(s_1,s_2)=(\alpha_1 s_1+\beta_1,\ \alpha_2 s_2+\beta_2)$. If the bargaining problem $\langle S',d'\rangle$ is obtained from $\langle S,d\rangle$ by this transformation, that is $S'=L(S)$ and $d'=L(d)$, then $f_i(S',d')=\alpha_i f_i(S,d)+\beta_i$ for $i=1,2$.
--   2. **SYM (symmetry).** If $\langle S,d\rangle$ is symmetric, meaning $d_1=d_2$ and $(s_1,s_2)\in S$ if and only if $(s_2,s_1)\in S$, then $f_1(S,d)=f_2(S,d)$.
--   3. **IIA (independence of irrelevant alternatives).** If $\langle S,d\rangle$ and $\langle T,d\rangle$ are bargaining problems with $S\subseteq T$ and $f(T,d)\in S$, then $f(S,d)=f(T,d)$.
--   4. **PAR (Pareto efficiency).** If $\langle S,d\rangle$ is a bargaining problem, $s,t\in S$, and $t_i>s_i$ for $i=1,2$, then $f(S,d)\neq s$.
--
--   **Theorem.** There is a unique bargaining solution $f^N$ satisfying INV, SYM, IIA and PAR. For every $\langle S,d\rangle\in\mathcal{B}$, the point $f^N(S,d)$ is the unique maximizer of the Nash product over the points of $S$ that weakly dominate the disagreement point:
--
--   $$
--   f^N(S,d)=\mathop{\arg\max}_{s\in S,\ s_1\ge d_1,\ s_2\ge d_2}\,(s_1-d_1)(s_2-d_2).
--   $$
--
--   Nash's theorem is the cornerstone of axiomatic bargaining theory. It singles out, from purely normative requirements, the division of the gains from cooperation that maximizes the product of the players' utility gains over disagreement, and it is the benchmark against which other axiomatic solutions (Kalai–Smorodinsky, egalitarian) and strategic bargaining models (Rubinstein's alternating offers) are compared.
--
--   **Formalization Note** Points of $\mathbb{R}^2$ are pairs in `ℝ × ℝ`. The set $\mathcal{B}$ is a variable `B` fixed by the hypothesis `hB`, and a bargaining solution is a function on the subtype `↥B`, evaluated at a problem $\langle S,d\rangle$ with membership proof `h` as `g ⟨(S, d), h⟩`. The conclusion provides an `f` such that a function `g` satisfies the five conditions ($g(S,d)\in S$ together with INV, SYM, IIA, PAR) if and only if `g = f`; this encodes existence and uniqueness. It then states that $f(S,d)\ge d$ componentwise and that every other $s\in S$ with $s\ge d$ has a strictly smaller Nash product, which encodes the argmax formula including the uniqueness of the maximizer. In INV the transformed pair is assumed to be a bargaining problem, as in the source (it always is one).
-- source:
--   J. F. Nash, 'The Bargaining Problem', Econometrica 18(2) (1950), 155–162. Statement and axioms as in M. J. Osborne and A. Rubinstein, Bargaining and Markets, Academic Press, 1990, Chapter 2 'The Axiomatic Approach: Nash's Solution': Section 2.2 (bargaining problems and bargaining solutions), Section 2.3 (axioms INV, SYM, IIA, PAR), Theorem 2.3.

import Mathlib

theorem NashBargaining.nash_bargaining_solution_unique
    (B : Set (Set (ℝ × ℝ) × (ℝ × ℝ)))
    (hB : B = {P | IsCompact P.1 ∧ Convex ℝ P.1 ∧ P.2 ∈ P.1 ∧
      ∃ s ∈ P.1, P.2.1 < s.1 ∧ P.2.2 < s.2}) :
    ∃ f : B → ℝ × ℝ,
      (∀ g : B → ℝ × ℝ,
        (-- g is a bargaining solution: it selects a point of S
         (∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), g ⟨(S, d), h⟩ ∈ S) ∧
         -- INV: invariance under positive affine rescalings of the two utilities
         (∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B)
            (α₁ α₂ β₁ β₂ : ℝ) (L : ℝ × ℝ → ℝ × ℝ), 0 < α₁ → 0 < α₂ →
            (∀ s : ℝ × ℝ, L s = (α₁ * s.1 + β₁, α₂ * s.2 + β₂)) →
            ∀ h' : (L '' S, L d) ∈ B, g ⟨(L '' S, L d), h'⟩ = L (g ⟨(S, d), h⟩)) ∧
         -- SYM: symmetric problems get symmetric outcomes
         (∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), d.1 = d.2 →
            (∀ s₁ s₂ : ℝ, (s₁, s₂) ∈ S ↔ (s₂, s₁) ∈ S) →
            (g ⟨(S, d), h⟩).1 = (g ⟨(S, d), h⟩).2) ∧
         -- IIA: independence of irrelevant alternatives
         (∀ (S T : Set (ℝ × ℝ)) (d : ℝ × ℝ) (hS : (S, d) ∈ B) (hT : (T, d) ∈ B),
            S ⊆ T → g ⟨(T, d), hT⟩ ∈ S → g ⟨(S, d), hS⟩ = g ⟨(T, d), hT⟩) ∧
         -- PAR: Pareto efficiency (a point of S strictly improved upon by some t ∈ S is never chosen)
         (∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), ∀ s ∈ S, ∀ t ∈ S,
            s.1 < t.1 → s.2 < t.2 → g ⟨(S, d), h⟩ ≠ s))
        ↔ g = f) ∧
      -- the unique such solution is the maximizer of the Nash product
      ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B),
        d.1 ≤ (f ⟨(S, d), h⟩).1 ∧ d.2 ≤ (f ⟨(S, d), h⟩).2 ∧
        ∀ s ∈ S, d.1 ≤ s.1 → d.2 ≤ s.2 → s ≠ f ⟨(S, d), h⟩ →
          (s.1 - d.1) * (s.2 - d.2) <
            ((f ⟨(S, d), h⟩).1 - d.1) * ((f ⟨(S, d), h⟩).2 - d.2) := by sorry
