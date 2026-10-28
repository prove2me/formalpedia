-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Continuous_subanalytic_compl
-- name    : NonsmoothLojasiewicz.Continuous.subanalytic_compl
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-28T05:45:45.213219+00:00
-- url     : https://prove2.me/theorems/e9c3d232-d2a5-47db-9caf-2affa3d457fc
-- title:
--   Gabrielov's theorem of the complement: the complement of a subanalytic set is subanalytic
-- statement:
--   Let $X$ be a finite-dimensional real normed space and let $A \subseteq X$ be subanalytic (in the sense of `IsSubanalytic`: locally a projection of a bounded semianalytic set). Then the complement
--
--   $$X \setminus A$$
--
--   is subanalytic.
--
--   Role: the parent's proof expresses its exceptional sets with quantifiers (sets of points for which every nearby subgradient satisfies a bound); turning a universal quantifier into a projection needs the complement theorem.
--
--   **Formalization Note**: the source states the theorem on a real analytic manifold $M$; here $M$ is a finite-dimensional real normed space, which is the case the parent uses.
-- source:
--   E. Bierstone, P. D. Milman, Semianalytic and subanalytic sets, Publ. Math. IHES 67 (1988) 5-42, https://www.numdam.org/item/10.1007/BF02699126.pdf, Theorem 3.10 (Theorem of the complement), p. 19; also J. Bolte, A. Daniilidis, A. Lewis, The Lojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205-1223, https://people.orie.cornell.edu/aslewis/publications/07-lojasiewicz.pdf, p. 1207 (Gabrielov theorem)

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic

namespace NonsmoothLojasiewicz.Continuous

theorem subanalytic_compl {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (A : Set X) (hA : IsSubanalytic A) : IsSubanalytic Aᶜ := by sorry

end NonsmoothLojasiewicz.Continuous
