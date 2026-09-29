-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_etale_typeGroup_nsmul_eq_one_iff_of_isUnit
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_etale_typeGroup_nsmul_eq_one_iff_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/3da26110-c5f4-5604-be53-2162634884da
-- title:
--   Étale-local splitting of the n-torsion of an abelian scheme
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, equipped with a relative group law $L$ (a group structure on $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ for every $t : T \to \operatorname{Spec} S$, with multiplication, unit and inverse satisfying the group axioms and compatible with precomposition in $T$), assumed commutative, and satisfying the property bundle: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law exists. Suppose every fibre $f^{-1}(s)$ has topological Krull dimension $g$, and let $n > 0$ be such that the image of $n$ in $S$ is a unit; let $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ have all values equal to $n$, so that $K(\delta) = (\prod_i \mathbb{Z}/\delta i) \times (\prod_i \mathbb{Z}/\delta i) \cong (\mathbb{Z}/n)^{g} \times (\mathbb{Z}/n)^{g}$. Then there exist a commutative $S$-algebra $S'$ which is faithfully flat and étale over $S$, and a family $(x_h)_{h \in K(\delta)}$ of morphisms $\operatorname{Spec} S' \to A$ over $\operatorname{Spec} S$, such that: (i) $h \mapsto x_h$ is a homomorphism, $x_0$ being the unit and $x_{h+h'} = L(x_h, x_{h'})$; (ii) for every algebraically closed field $k$ and every ring homomorphism $S' \to k$, the composites $\operatorname{Spec} k \to \operatorname{Spec} S' \to A$ of the $x_h$ are pairwise distinct; and (iii) for every commutative $S'$-algebra $R$ and every morphism $y : \operatorname{Spec} R \to A$ over the composite structure map $\operatorname{Spec} R \to \operatorname{Spec} S$, one has $n \cdot y = 1$ (the $n$-fold product of $y$ with itself for $L$, equal to the unit) if and only if there are finitely many elements $r_1,\dots,r_m \in R$ generating the unit ideal such that for each $j$ there is $h \in K(\delta)$ with $y$ and $x_h$ becoming equal after base change to the localisation of $R$ away from $r_j$.
--
--   This is the statement that for $n$ invertible on the base the $n$-torsion of an abelian scheme of relative dimension $g$ is étale-locally the constant group $(\mathbb{Z}/n)^{g} \times (\mathbb{Z}/n)^{g}$, formulated in the shape of the project's 'is of type $\delta$' conditions with membership in the kernel of the polarisation replaced by the condition $n \cdot y = 1$. It is used in the construction identifying a polarised abelian scheme as being of the relevant type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_etale_typeGroup_nsmul_eq_one_iff_of_isUnit.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_etale_typeGroup_nsmul_eq_one_iff_of_isUnit
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit ((n : ℕ) : S))
    (δ : Fin g → ℕ) (hδ : ∀ i, δ i = n) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S') (_ : Module.FaithfullyFlat S S') (_ : Algebra.Etale S S')
      (x : PolarisedAbelianScheme.typeGroup δ → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) f),
      (x 0 = L.one _ ∧ ∀ h h' : PolarisedAbelianScheme.typeGroup δ, x (h + h') = L.mul _ (x h) (x h')) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (h h' : PolarisedAbelianScheme.typeGroup δ),
        Spec.map (CommRingCat.ofHom sk) ≫ (x h).1 = Spec.map (CommRingCat.ofHom sk) ≫ (x h').1 → h = h') ∧
      (∀ (R : Type) [CommRing R] [Algebra S' R]
        (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap S' R).comp (algebraMap S S')))) f),
        L.nsmul _ n y = L.one _ ↔
          ∃ (m : ℕ) (r : Fin m → R), Ideal.span (Set.range r) = ⊤ ∧ ∀ j, ∃ h : PolarisedAbelianScheme.typeGroup δ,
            Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r j)))) ≫ y.1 =
              Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away (r j))).comp (algebraMap S' R))) ≫ (x h).1) := by sorry
