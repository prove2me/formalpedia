-- Prove2me | Theorems.Thm_MixedCloning_Optimal_branching
-- name    : MixedCloning.Optimal.branching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:49.704209+00:00
-- url     : https://prove2.me/theorems/5aa6ef68-b516-496e-af0e-f439be8b0411
-- title:
--   Section 2.4.2 — multiplicity-free unitary branching
-- statement:
--   Let $d\ge0$ and let $\lambda$ be a Young diagram of height at most $d+1$. Restrict $Q^{d+1}_\lambda$ to the subgroup $U(d)$ acting on the first $d$ coordinates and fixing the last. There exist isometric intertwiners $E_{\lambda'\subseteq\lambda}:Q^d_{\lambda'}\to Q^{d+1}_\lambda$ for all interlacing diagrams $\lambda'$ of height at most $d$, with mutually orthogonal images and
--
--   $$\sum_{\lambda'\preceq\lambda}E_{\lambda'\subseteq\lambda}E_{\lambda'\subseteq\lambda}^\dagger=I_\lambda.$$
--
--   Thus the restriction is the direct sum of precisely these representations, each with multiplicity one. This supplies the embeddings without assuming that such a family exists.
--
--   Differences from the source:
--   - encoding: U(d) restricted to U(d−1) → U(d+1) restricted to U(d); reason: successor indexing avoids truncated subtraction
--   - encoding: unitary direct-sum isomorphism → isometric intertwiners with orthogonal images summing to the identity; reason: these are equivalent descriptions of the displayed decomposition
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 14, Section 2.4.2, branching-rule display

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem branching (d : ℕ) (L : YoungDiagram) (hL : height L ≤ d+1) :
    ∃ E : BranchFamily d L, IsBranchFamily d L E ∧
      (∀ M N, M ≠ N → (E M)ᴴ * E N = 0) ∧
      (∑ M : {M : YoungDiagram // M ∈ branches d L}, E M * (E M)ᴴ) = 1 := by sorry

end MixedCloning.Optimal
