-- Prove2me | Theorems.Thm_MICPRep_Periodic_theorem_5_1
-- name    : MICPRep.Periodic.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:46.276521+00:00
-- url     : https://prove2.me/theorems/bb8c97c2-94a4-4916-9873-507dd2f7ca48
-- title:
--   Theorem 5.1, p. 16 — a closed rational MICP-R set whose convex subsets have uniformly bounded diameter is a finite union of compact convex sets and closed periodic sets
-- statement:
--   Let $S \subseteq \mathbb R^n$ be closed and rational MICP-R. If there is a uniform upper bound $D$ on the diameter of every convex subset of $S$, then there are $k_1, k_2 \in \mathbb Z_+$, compact convex sets $C_1, \dots, C_{k_1}$ and closed periodic sets $S_1, \dots, S_{k_2}$ such that
--   $$S = \Bigl(\bigcup_{j=1}^{k_1} C_j\Bigr) \cup \Bigl(\bigcup_{i=1}^{k_2} S_i\Bigr). \tag{5.2}$$
--
--   This is the paper's main structural result on rational MICP-R sets. It excludes pathological sets such as $\{x \in \mathbb Z : f(x\sqrt 2) \notin (0.4, 0.6)\}$ from rational MICP representability, characterizes the compact rational MICP-R sets and separates rational MICP from rational MILP on subsets of $\mathbb N$.
--
--   **Formalization Note** The diameter is the extended Euclidean diameter (`Metric.ediam`), so an unbounded convex subset violates the bound; the bound $D$ is one real number for all convex $C \subseteq S$. Periodic means a nonzero $u$ with $x + \lambda u \in S$ for all $\lambda \in \mathbb N$; rational MICP-R uses Definition 5.1 over all rational affine images. Either $k_1$ or $k_2$ may be $0$, and the pieces need not be disjoint or nonempty.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, p. 16, Theorem 5.1, (5.2)

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- Theorem 5.1, p. 16. -/
theorem theorem_5_1 {n : ℕ} (S : Set (Pt n)) (hclosed : IsClosed S) (hrat : IsRationalMICPR S)
    (hdiam : ∃ D : ℝ, ∀ C ⊆ S, Convex ℝ C → Metric.ediam C ≤ ENNReal.ofReal D) :
    ∃ (k₁ k₂ : ℕ) (C : Fin k₁ → Set (Pt n)) (T : Fin k₂ → Set (Pt n)),
      (∀ j, IsCompact (C j) ∧ Convex ℝ (C j)) ∧
      (∀ i, IsClosed (T i) ∧ IsPeriodic (T i)) ∧
      S = (⋃ j, C j) ∪ (⋃ i, T i) := by sorry

end MICPRep.Periodic
