-- Prove2me | Theorems.Thm_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul
-- name    : HopfOrder.exists_equiv_algHom_apply_eq_and_toConv_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/83b45ef9-74a4-5d3d-99c7-19f559dd8885
-- title:
--   Points of a Hopf order agree with generic-fibre points
-- statement:
--   Let $R$ be a principal ideal domain with fraction field $K$, let $A$ be a commutative ring carrying a Hopf algebra structure over $K$ together with a compatible $R$-algebra structure ($R \to K \to A$ a scalar tower), and let $S$ be an $R$-subalgebra of $A$ that is finite as an $R$-module, whose $K$-span inside $A$ is all of $A$, and which satisfies: for every $x \in S$ the comultiplication $\Delta(x) \in A \otimes_K A$ lies in the image of the algebra map $S \otimes_R S \to A \otimes_K A$ induced by the two inclusions $S \hookrightarrow A \rightrightarrows A \otimes_K A$, the antipode maps $S$ into $S$, and the counit maps $S$ into the image of $R$ in $K$; these are exactly the hypotheses under which [`HopfOrder.hopfAlgebraOfFinite`](def/HopfAlgebra_HopfOrderData.html#L1091) equips $S$ with a Hopf $R$-algebra structure, which is the structure used in the conclusion. Let $L$ be a commutative ring that is a $K$-algebra and an $R$-algebra compatibly, and let $P$ be an $R$-subalgebra of $L$ containing every element of $L$ integral over $R$. Then there is a bijection $e$ from $K$-algebra homomorphisms $A \to L$ onto $R$-algebra homomorphisms $S \to P$ such that $e(f)(x) = f(x)$ in $L$ for all $x \in S$, such that $e$ carries the convolution product of $f$ and $g$ to the convolution product of $e(f)$ and $e(g)$, and such that $e$ sends the convolution unit to the convolution unit.
--
--   This is the statement that the points of a Hopf order in a commutative Hopf $K$-algebra, valued in an integrally closed $R$-subalgebra $P$ of a $K$-algebra $L$, are the same, as a convolution monoid, as the $L$-points of the generic fibre: in scheme language, $\mathcal{G}(P) = G(L)$ for $\mathcal{G} = \operatorname{Spec} S$ finite flat over $R$ with generic fibre $G = \operatorname{Spec} A$. It is used in [`HopfAlgebra.exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step`](thm.html#HopfAlgebra.exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step), in the comparison of a finite flat model with its generic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfOrderData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem HopfOrder.exists_equiv_algHom_apply_eq_and_toConv_mul
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    {L : Type*} [CommRing L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (P : Subalgebra R L) (hP : ∀ x : L, IsIntegral R x → x ∈ P) :
    letI := HopfOrder.hopfAlgebraOfFinite S hcomul hcounit hanti
    ∃ e : (A →ₐ[K] L) ≃ (↥S →ₐ[R] ↥P),
      (∀ (f : A →ₐ[K] L) (x : ↥S), ((e f x : ↥P) : L) = f (x : A)) ∧
      (∀ f g : A →ₐ[K] L,
          WithConv.toConv (e (WithConv.ofConv (WithConv.toConv f * WithConv.toConv g)))
            = WithConv.toConv (e f) * WithConv.toConv (e g)) ∧
      WithConv.toConv (e (WithConv.ofConv (1 : WithConv (A →ₐ[K] L)))) = 1 := by sorry
