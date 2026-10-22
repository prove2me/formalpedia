-- Prove2me | Theorems.Thm_LoopTwoGroup_Equiv_theorem_5_1
-- name    : LoopTwoGroup.Equiv.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:57.60386+00:00
-- url     : https://prove2.me/theorems/403146bf-8d71-4830-8e45-583f19353fa2
-- title:
--   Theorem 5.1 — strictly exact EΩ𝔤 → P_k𝔤 → 𝔤_k and equivalence
-- statement:
--   Let $\mathfrak g$ be a finite-dimensional real simple Lie algebra with an invariant positive-definite inner product, and let $k\in\mathbb R$. There are homomorphisms
--   $$0\longrightarrow E\Omega\mathfrak g\xrightarrow{\lambda}\mathcal P_k\mathfrak g\xrightarrow{\phi}\mathfrak g_k\longrightarrow 0$$
--   that are strictly exact on both the object vector spaces and the morphism vector spaces: $\lambda$ is injective, $\operatorname{im}\lambda=\ker\phi$, and $\phi$ is surjective in each degree; the composite is the zero homomorphism, including its degree-two component. Moreover $E\Omega\mathfrak g$ is equivalent to the trivial Lie 2-algebra and $\phi$ is an equivalence.
--
--   This is the Lie-algebra-level main result of the paper. It relates the infinite-dimensional path construction to the finite-dimensional skeletal algebra without discarding the central integral term.
--
--   **Formalization Note** Lie 2-algebras and their equivalences are represented by the 2-term $L_\infty$ components of §2 and Theorem 2.10; the categorical equivalence theorem itself is not re-proved. The path algebra is defined by Proposition 4.2's formulas, and $k$ is real. The inner-product normalization used for the group-level extension is not imposed here.
-- source:
--   Baez–Crans–Stevenson–Schreiber, From Loop Groups to 2-Groups, arXiv:math/0504123v3, p. 25, Theorem 5.1 and the immediately following definition of strictly exact

import Mathlib
import Definitions.Def_LoopTwoGroup_Equiv_Model

namespace LoopTwoGroup.Equiv

variable {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
  [FiniteDimensional ℝ g]

/-- Theorem 5.1, p. 25: the strictly exact sequence and both equivalences. -/
theorem theorem_5_1 (L : InvLieBracket g) (k : ℝ) :
    ∃ (Λ : LInfHom (EOmega L) (Pk L k)) (Φ : LInfHom (Pk L k) (gk L k)),
      Function.Injective Λ.f0 ∧ Function.Injective Λ.f1 ∧
      LinearMap.range Λ.f0 = LinearMap.ker Φ.f0 ∧
      LinearMap.range Λ.f1 = LinearMap.ker Φ.f1 ∧
      Function.Surjective Φ.f0 ∧ Function.Surjective Φ.f1 ∧
      (∀ a b, compF2 Λ Φ a b = 0) ∧
      Equivalent (EOmega L) trivialData ∧ IsEquivalence Φ := by sorry

end LoopTwoGroup.Equiv
