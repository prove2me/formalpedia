-- Prove2me | Theorems.Thm_GelfandVNA_Duality_proposition_3_9
-- name    : GelfandVNA.Duality.proposition_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:57.78614+00:00
-- url     : https://prove2.me/theorems/c8210dbe-b911-4f90-ba95-aa55f024015f
-- title:
--   Proposition 3.9, p. 24 — the predual A_* is in bijection with complex continuous valuations on ProjAlg(A)
-- statement:
--   Let $A$ be a commutative von Neumann algebra with predual $A_*$, identified with the space of normal functionals on $A$. Restriction along the inclusion $\mathsf{ProjAlg}(A)\hookrightarrow A$ is a bijection
--   $$A_*\ \xrightarrow{\ \sim\ }\ \{\text{complex continuous valuations on } \mathsf{ProjAlg}(A)\}.$$
--   That is: the restriction $p\mapsto\varphi(p)$ of every normal functional $\varphi$ is a continuous valuation, and every complex continuous valuation $\nu$ on $\mathsf{ProjAlg}(A)$ is the restriction of exactly one normal functional.
--
--   Here a complex valuation $\nu$ satisfies $\nu(0)=0$ and $\nu(x)+\nu(y)=\nu(x\vee y)+\nu(x\wedge y)$, and it is continuous if $\nu(\sup I)=\lim_{x\in I}\nu(x)$ for every directed subset $I$ (Definition 2.19).
--
--   This identifies the predual with an object defined from the Boolean algebra alone; it gives the predual of $L^\infty$ in Theorem 3.20.
--
--   **Formalization Note** $A_*$ is represented by the normal functionals $A\to\mathbb C$ of the VNA module; uniqueness is uniqueness of the functional.
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, p. 24, Proposition 3.9

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
import Definitions.Def_GelfandVNA_Duality_VNA

namespace GelfandVNA.Duality

open QAlgorithms.Papers.Independent.Support21.P20

universe u

/-- Proposition 3.9, p. 24: for a commutative von Neumann algebra `A`, restriction along
`ProjAlg(A) → A` is a bijection from the predual `A_*` (the normal functionals) onto the complex
continuous valuations on `ProjAlg(A)`. -/
theorem proposition_3_9 (A : Type u) [CommCStarAlgebra A] [WStarAlgebra A] :
    (∀ φ : A → ℂ, IsNormalFunctional φ → IsContinuousValuation (fun p : ProjAlg A => φ p.val)) ∧
    (∀ ν : ProjAlg A → ℂ, IsContinuousValuation ν →
      ∃! φ : A → ℂ, IsNormalFunctional φ ∧ ∀ p : ProjAlg A, φ p.val = ν p) := by sorry

end GelfandVNA.Duality
