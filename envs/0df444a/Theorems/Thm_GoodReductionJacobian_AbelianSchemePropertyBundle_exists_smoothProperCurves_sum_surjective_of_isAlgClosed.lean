-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_smoothProperCurves_sum_surjective_of_isAlgClosed
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_smoothProperCurves_sum_surjective_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/c3bfd4ee-fe5d-5e9a-88d5-6a144f9f10f1
-- title:
--   Every k-point of an abelian variety is a sum of curve points
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme, let $f : A \to \operatorname{Spec} k$ be a morphism, and let $L$ be a relative group law for $f$: an assignment, to every $k$-scheme $t : T \to \operatorname{Spec} k$, of a multiplication, a unit and an inversion on the set of $T$-points $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$, satisfying associativity, both unit laws and left inversion, and with multiplication compatible with precomposition along any $\psi : T' \to T$ over $\operatorname{Spec} k$. Assume the bundle `AbelianSchemePropertyBundle` for $f$, namely that $f$ is smooth and proper, that the fibre $f^{-1}(s)$ over each point $s$ of $\operatorname{Spec} k$ is connected (in the topological sense, i.e. nonempty and connected), and that some relative group law for $f$ exists; and let $g$ be a natural number such that each such fibre has topological Krull dimension $g$. Then there are an $n$, schemes $C_0,\dots,C_{n-1}$ with structure morphisms $c_i : C_i \to \operatorname{Spec} k$ and morphisms $\nu_i : C_i \to A$ over $\operatorname{Spec} k$ (that is, $\nu_i$ followed by $f$ equals $c_i$), such that each $c_i$ is proper and smooth of relative dimension $1$ with $C_i$ integral, and such that for every $k$-point $P$ of $A$ (a section of $f$ over the identity of $\operatorname{Spec} k$) there are $k$-points $y_i$ of $C_i$ with $P$ equal to the right-folded product, under $L$'s multiplication on $k$-points and starting from $L$'s unit, of the images $\nu_i \circ y_i$.
--
--   This is the statement that an abelian variety over an algebraically closed field is swept out by finitely many smooth proper integral curves: the sum map $\prod_i C_i(k) \to A(k)$ is surjective. It is used in the project to reduce assertions about all $k$-points of an abelian scheme to assertions about points coming from curves, in the construction of homomorphisms out of such a group law and in an approximation argument over the complex numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_smoothProperCurves_sum_surjective_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_smoothProperCurves_sum_surjective_of_isAlgClosed
    (k : Type) [Field k] [IsAlgClosed k]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (hA : AbelianSchemePropertyBundle k f) (g : ℕ)
    (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g) :
    ∃ (n : ℕ) (C : Fin n → Scheme.{0}) (c : ∀ i : Fin n, C i ⟶ Spec (CommRingCat.of k))
      (ν : ∀ i : Fin n, C i ⟶ A) (hν : ∀ i : Fin n, ν i ≫ f = c i),
      (∀ i : Fin n, IsProper (c i) ∧ SmoothOfRelativeDimension 1 (c i) ∧ IsIntegral (C i)) ∧
      ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
        ∃ y : ∀ i : Fin n, SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (c i),
          (List.ofFn (fun i : Fin n => mapPt (ν i) (hν i) (y i))).foldr
              (fun Q R => L.mul (𝟙 (Spec (CommRingCat.of k))) Q R)
              (L.one (𝟙 (Spec (CommRingCat.of k)))) = P := by sorry
