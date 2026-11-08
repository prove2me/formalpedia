-- Prove2me | Theorems.Thm_LaarakkerOttenVanDenBerg2026_theorem_11_inductive_types
-- name    : LaarakkerOttenVanDenBerg2026.theorem_11_inductive_types
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-07T15:42:44.507434+00:00
-- url     : https://prove2.me/theorems/3be38503-8554-418d-9546-2a8d51d99137
-- title:
--   Theorem 11 & Polynomial W-Type Corollary: Initial Algebras via Existential Size Quantification
-- statement:
--   **Theorem 11 & Polynomial $W$-Type Corollary (Section 3.3, p. 12)**:
--   In any `ParametricSizeTheory` $P$:
--   1. **Theorem 11**: For every wild endofunctor $F : U \to U$ that weakly commutes with $\exists$, the $F$-algebra `muAlg` with carrier $\mu F := \exists i.\,(\mu^\Diamond F)\,i$ is an initial $F$-algebra, and its structure map $\mathsf{in} : \mathrm{El}(F(\mu F)) \to \mathrm{El}(\mu F)$ is a tracked half-adjoint equivalence.
--   2. **Polynomial $W$-Type Corollary**: Every polynomial endofunctor $P_{A, B}(X) := \Sigma a : A.\,(B(a) \to X)$ (finitely or infinitely branching) weakly commutes with $\exists$, and therefore admits an initial algebra ($W$-type) with carrier $\exists i.\,(\mu^\Diamond P_{A, B})\,i$.
-- source:
--   Bastiaan Laarakker, Daniël Otten, and Benno van den Berg, 'Constructing (Co)inductive Types via Large Sizes', FSCD 2026 (arXiv:2602.18921), Section 3.3, Theorem 11 & Polynomial W-Type Corollary (p. 12)

import Definitions.Def_LaarakkerOttenVanDenBerg2026_Encoding

namespace LaarakkerOttenVanDenBerg2026

universe u v

theorem theorem_11_inductive_types
    (P : ParametricSizeTheory.{u, v}) :
    (∀ (F : WildEndofunctor P.toSizeCoreTheory)
      (hF : WeaklyCommutesEx P.toSizeCoreTheory F),
      Nonempty (IsInitialFAlg (muAlg P.toSizeCoreTheory hF)) ∧
      Nonempty (IsTrackedHAEquiv P.toSizeCoreTheory (muAlg P.toSizeCoreTheory hF).str)) ∧
    (∀ (A : P.U) (B : P.El A → P.U),
      ∃ (hPoly : WeaklyCommutesEx P.toSizeCoreTheory
          (polyEndofunctor P.toSizeCoreTheory A B)),
        Nonempty (IsInitialFAlg (muAlg P.toSizeCoreTheory hPoly)) ∧
        Nonempty (IsTrackedHAEquiv P.toSizeCoreTheory (muAlg P.toSizeCoreTheory hPoly).str)) := by
  sorry

end LaarakkerOttenVanDenBerg2026
