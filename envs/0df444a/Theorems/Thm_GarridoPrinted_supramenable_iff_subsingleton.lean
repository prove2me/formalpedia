-- Prove2me | Theorems.Thm_GarridoPrinted_supramenable_iff_subsingleton
-- name    : GarridoPrinted.supramenable_iff_subsingleton
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T21:52:00.465989+00:00
-- url     : https://prove2.me/theorems/ea6361ba-eaff-4873-ac72-c09a0dc0ad6e
-- title:
--   Garrido, Definition 3.9 as printed — with measures valued in [0, 1], only the trivial group is supramenable
-- statement:
--   For a group $G$, the following are equivalent: for every nonempty $A \subseteq G$ there is a finitely additive, left-invariant $m : \mathcal P(G) \to [0, \infty]$ with $m(s) \le 1$ for every $s \subseteq G$ and $m(A) = 1$; and $G$ has at most one element.
--
--   `IsFinitelyAdditiveMeasure` ($m(\emptyset) = 0$ and $m(s \cup t) = m(s) + m(t)$ for disjoint $s, t$) and `IsInvariant G m` ($m(g s) = m(s)$ for all $g$ and $s$) are from the Garrido amenability definitions bundle; the bound $m(s) \le 1$ is the codomain $[0, 1]$ of the printed definition, written inside $[0, \infty]$.
--
--   Garrido writes on p. 11: “**Definition 3.9.** A group $G$ is *supramenable* if for every $\emptyset \neq A \subseteq G$ there is a finitely additive left-invariant measure $\mu : \mathcal P(G) \to [0, 1]$ such that $\mu(A) = 1$.” Read literally this is satisfied only by the trivial group: taking $A = \{1\}$, invariance gives $\mu(\{g\}) = 1$ for every $g$, and two distinct points would give $\mu(\{1, g\}) = 2$. The bundle's `IsSupramenable` therefore takes values in $[0, \infty]$, as in Rosenblatt's definition, under which Theorem 3.10(2) (`Garrido.isSupramenable_of_isExponentiallyBounded`: finitely generated groups of subexponential growth are supramenable, so $\mathbb Z$ is) holds; this theorem records why the printed codomain cannot be the intended one.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 11, Definition 3.9; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Amenability

namespace GarridoPrinted

theorem supramenable_iff_subsingleton (G : Type*) [Group G] :
    (∀ A : Set G, A.Nonempty → ∃ m : Set G → ENNReal,
      Garrido.IsFinitelyAdditiveMeasure m ∧ (∀ s, m s ≤ 1) ∧ m A = 1 ∧ Garrido.IsInvariant G m) ↔
      Subsingleton G := by
  sorry

end GarridoPrinted
