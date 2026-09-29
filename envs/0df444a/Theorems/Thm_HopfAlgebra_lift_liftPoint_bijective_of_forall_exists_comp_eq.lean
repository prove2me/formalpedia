-- Prove2me | Theorems.Thm_HopfAlgebra_lift_liftPoint_bijective_of_forall_exists_comp_eq
-- name    : HopfAlgebra.lift_liftPoint_bijective_of_forall_exists_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/87fe431c-a0ae-58ee-a10b-70fafc32d54e
-- title:
--   Evaluation isomorphism for a D-stable subset of split points
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $D$ be a subgroup of the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$ whose fixed intermediate field is the bottom one, i.e. $L^{D}$ is the image of $K$ in $L$. Let $A$ be a commutative ring with a $K$-algebra structure which is finite as a $K$-module, let $P$ be a finite type, and let $\mathrm{pt} : P \to (A \to_{\mathrm{alg}[K]} L)$ be an injective family of $K$-algebra maps $A \to L$. Assume that the $L$-algebra map $L \otimes_K A \to (P \to L)$ determined by the structure map $L \to (P \to L)$ onto constants and by $a \mapsto (\mathrm{pt}\,p\,(a))_{p \in P}$ is bijective. Let $S \subseteq P$ be a subset that is stable under $D$ in the sense that for every $\sigma \in D$ and every $p \in S$ there is $p' \in S$ with $\mathrm{pt}\,p'\,(a) = \sigma(\mathrm{pt}\,p\,(a))$ for all $a \in A$. Write $I_S = \{a \in A : \nu(a) = 0 \text{ for all } \nu \in \mathrm{pt}(S)\}$, the ideal [`HopfAlgebra.vanishingIdealOfPoints (pt '' S)`](def/HopfAlgebra_CharacterClosure.html#L16). Then the $L$-algebra map $L \otimes_K (A/I_S) \to (S \to L)$ determined by the constants $L \to (S \to L)$ together with the maps [`HopfAlgebra.liftPoint`](def/HopfAlgebra_CharacterClosure.html#L28), namely the factorisations of $\mathrm{pt}\,s$ through $A/I_S$ for $s \in S$, is bijective.
--
--   This is the Galois-descent step asserting that the subalgebra of functions on a $D$-stable subset of the points of a finite $K$-algebra split by $L$ is again split by $L$, with point set exactly that subset; the hypothesis $L^{D} = K$ plays the role of the Galois condition, and no Hopf or monoid structure on the set of points is involved. It is used in the construction of character closures of bialgebras over perfect fields and in the base-change description of Hopf quotient systems attached to $p$-divisible groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_lift_liftPoint_bijective_of_forall_exists_comp_eq.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CharacterClosure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem HopfAlgebra.lift_liftPoint_bijective_of_forall_exists_comp_eq
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D : Subgroup (L ≃ₐ[K] L)) (hD : IntermediateField.fixedField D = ⊥)
    {A : Type*} [CommRing A] [Algebra K A] [Module.Finite K A]
    {P : Type*} [Finite P] (pt : P → (A →ₐ[K] L)) (hpt : Function.Injective pt)
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (Pi.algHom K _ fun p : P => pt p)
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (P → L)))
    (S : Set P) (hstab : ∀ σ : L ≃ₐ[K] L, σ ∈ D → ∀ p ∈ S, ∃ p' ∈ S, ∀ a : A, pt p' a = σ (pt p a)) :
    Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId L (↥S → L))
        (Pi.algHom K _ fun s : ↥S =>
          HopfAlgebra.liftPoint (pt '' S) (pt s.1) (Set.mem_image_of_mem pt s.2))
        (fun _ _ => Commute.all _ _) :
        L ⊗[K] (A ⧸ HopfAlgebra.vanishingIdealOfPoints (pt '' S)) →ₐ[L] (↥S → L)) := by sorry
