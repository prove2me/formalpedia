-- Prove2me | Theorems.Thm_HopfAlgebra_exists_fVectStructure_of_pointAction_of_bijective_evalPoints
-- name    : HopfAlgebra.exists_fVectStructure_of_pointAction_of_bijective_evalPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/74910ba2-7071-516e-8613-5db626ddb328
-- title:
--   Galois-equivariant F-action on points descends to an F-vector space structure
-- statement:
--   Let $K$ be a perfect field, write $\bar K$ for `AlgebraicClosure K`, and let $H$ be a commutative ring that is a Hopf algebra over $K$, finite as a $K$-module and cocommutative as a $K$-coalgebra. Let $V :=$ `WithConv (H →ₐ[K] AlgebraicClosure K)` denote the set of $\bar K$-points of $H$ equipped with its convolution monoid structure, assumed finite. Assume the evaluation map is bijective: the $\bar K$-algebra homomorphism $\bar K \otimes_K H \to (V \to \bar K)$ obtained from the structure map $\bar K \to (V \to \bar K)$ together with the product of the points $\nu \in V$ is a bijection. Let $F$ be a finite field and let $\mathrm{smulF} : F \to V \to V$ satisfy: $\mathrm{smulF}\,1 = \mathrm{id}$; $\mathrm{smulF}(ab) = \mathrm{smulF}\,a \circ \mathrm{smulF}\,b$; $\mathrm{smulF}\,0$ is constantly the convolution unit; $\mathrm{smulF}(a+b)\,x = (\mathrm{smulF}\,a\,x)\cdot(\mathrm{smulF}\,b\,x)$ in $V$; each $\mathrm{smulF}\,a$ is a monoid endomorphism of $V$ for convolution; and each $\mathrm{smulF}\,a$ is equivariant, in the sense that for every $\sigma \in \mathrm{Aut}(\bar K/K)$ and $x,y \in V$ with $y = \sigma \circ x$ pointwise on $H$, one also has $\mathrm{smulF}\,a\,y = \sigma \circ (\mathrm{smulF}\,a\,x)$ pointwise. Then there exists a [`HopfAlgebra.FVectStructure F K H`](def/HopfAlgebra_FVectStructure.html#L11), that is, a family of $K$-bialgebra endomorphisms $[a]$ of $H$ with $[1] = \mathrm{id}$, $[ab] = [a] \circ [b]$, $[0]$ the convolution unit of $H \to_{\mathrm{alg}} H$, and $[a+b] = [a] * [b]$ under convolution, which induces the given action on points: for all $a \in F$ and $x \in V$, the class of $x \circ [a]$ in $V$ equals $\mathrm{smulF}\,a\,x$.
--
--   This is the $F$-structure half of the dictionary between finite étale commutative group schemes over $K$ and finite Galois modules, in the form needed for Raynaud's notion of an $F$-vector space scheme: a Galois-equivariant $F$-action on the geometric points comes from an $F$-vector space structure on the Hopf algebra itself. It feeds into [`HopfAlgebra.hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField`](thm.html#HopfAlgebra.hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_fVectStructure_of_pointAction_of_bijective_evalPoints.lean

import Mathlib
import Definitions.Def_HopfAlgebra_FVectStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_fVectStructure_of_pointAction_of_bijective_evalPoints
    (K : Type u) [Field K] [PerfectField K]
    (H : Type v) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] [Coalgebra.IsCocomm K H]
    [Finite (WithConv (H →ₐ[K] AlgebraicClosure K))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure K) (WithConv (H →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
        (Pi.algHom K _
          fun ν : WithConv (H →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : H →ₐ[K] AlgebraicClosure K))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure K ⊗[K] H →ₐ[AlgebraicClosure K]
          (WithConv (H →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)))
    (F : Type) [Field F] [Fintype F]
    (smulF : F → WithConv (H →ₐ[K] AlgebraicClosure K) → WithConv (H →ₐ[K] AlgebraicClosure K))
    (h_one : ∀ x, smulF 1 x = x)
    (h_mul : ∀ (a b : F) x, smulF (a * b) x = smulF a (smulF b x))
    (h_zero : ∀ x, smulF 0 x = 1)
    (h_add : ∀ (a b : F) x, smulF (a + b) x = smulF a x * smulF b x)
    (h_pt_one : ∀ a : F, smulF a 1 = 1)
    (h_pt_mul : ∀ (a : F) x y, smulF a (x * y) = smulF a x * smulF a y)
    (h_gal : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : F)
        (x y : WithConv (H →ₐ[K] AlgebraicClosure K)),
        (∀ h : H, WithConv.ofConv y h = σ (WithConv.ofConv x h)) →
        ∀ h : H, WithConv.ofConv (smulF a y) h = σ (WithConv.ofConv (smulF a x) h)) :
    ∃ σF : HopfAlgebra.FVectStructure F K H,
      ∀ (a : F) (x : WithConv (H →ₐ[K] AlgebraicClosure K)),
        WithConv.toConv ((WithConv.ofConv x).comp (σF.act a : H →ₐ[K] H)) = smulF a x := by sorry
