-- Prove2me | Theorems.Thm_MazurTransfer_GaloisFixedOverPointDescent_exists_unique_descent
-- name    : MazurTransfer.GaloisFixedOverPointDescent.exists_unique_descent
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T22:12:24.942826+00:00
-- url     : https://prove2.me/theorems/7fa8cedf-57c5-4ce7-8d03-1af17983cbf5
-- title:
--   Galois-fixed over-category points descend uniquely over the same base
-- statement:
--   Let K/F be an arbitrary Galois extension, let X be a scheme over F with its specified structure morphism t, and let b be a K-point respecting t. If every F-automorphism of K fixes b, then b is scalar extension of a unique F-point respecting the same structure morphism: $$\forall\sigma\in\operatorname{Aut}_F(K),\ \sigma^*b=b\quad\Longrightarrow\quad\exists!a\in X(F),\ a_K=b.$$ No finite extension or finite-type hypothesis is added. The named downstream consumer is the original actual Picard fixed-point descent bridge and actual norm Kummer injectivity.
-- source:
--   Complete original MazurTheorem GaloisFixedOverPointDescent.exists_unique_descent statement and main proof, including the exact original binder order. The original scalar-extension constructor is retained with full type and value. Both scalarMap_epi and scalarExtension_injective helper full types and proof bodies are retained. Apache-2.0. Named downstream consumer: original actual Picard fixed_point_descends, rational-to-fixed group equivalence and actual norm Kummer injectivity.

import Definitions.Def_MazurTransfer_GaloisFixedOverPointScalarExtensionData
noncomputable section
open CategoryTheory AlgebraicGeometry
open MazurTransfer.FieldAutomorphismOverPointAction MazurTransfer.GaloisFixedOverPointDescent

theorem MazurTransfer.GaloisFixedOverPointDescent.exists_unique_descent {F K : Type} [Field F] [Field K] [Algebra F K]
    {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of F)) [IsGalois F K]
    (b : Over.mk (fieldBase F K) ⟶ Over.mk t)
    (hb : ∀ σ : K ≃ₐ[F] K, fieldAut F K σ ≫ b = b) :
    ∃! a : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Over.mk t,
      scalarOverMap F K ≫ a = b := by sorry
