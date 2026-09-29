-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_geomFibreH0Finrank_tensorPow_eq_pow_mul_of_hom_of_closedImmersionBySections
-- name    : GoodReductionJacobian.RelativeGroupLaw.geomFibreH0Finrank_tensorPow_eq_pow_mul_of_hom_of_closedImmersionBySections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/5750dc3c-e152-5b10-ba31-68208c4a4387
-- title:
--   Tensor powers on abelian fibres: h⁰ scales by d^g
-- statement:
--   Let $S$ be a commutative ring and let $f : A \to \operatorname{Spec} S$, $g : B \to \operatorname{Spec} S$ be morphisms of schemes equipped with relative group laws `LA`, `LB` in the sense of `RelativeGroupLaw` (functorial group structures on $T$-points over $\operatorname{Spec} S$, compatible with base change), both assumed commutative, and let both $f$ and $g$ satisfy `AbelianSchemePropertyBundle`, i.e. be smooth and proper with connected fibres and admit some relative group law. Let $\mathcal L_A$ be a module on $A$ that is invertible (locally isomorphic to the structure sheaf) and satisfies `ClosedImmersionBySections` over $f$, meaning that for some $N$ there is a `ProjPresentation` of $\mathcal L_A$ by $N+1$ global sections whose associated morphism to $\mathbb P^N_S$ is a closed immersion; likewise $\mathcal L_B$ on $B$ over $g$. Let $gA \in \mathbb N$ be such that every fibre of $f$ has topological Krull dimension $gA$. Let $S'$ be a commutative ring, $s : \operatorname{Spec} S' \to \operatorname{Spec} S$, and $\varphi : A \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to B$ a morphism over $\operatorname{Spec} S'$ (that is, $\varphi$ followed by $g$ equals the second projection followed by $s$) which is a homomorphism on points: for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and all $P, Q \in A(T)$ over $t' \circ s$, the $\varphi$-image of $\mathrm{LA}\text{-}\mathrm{mul}(P,Q)$ equals $\mathrm{LB}\text{-}\mathrm{mul}$ of the $\varphi$-images of $P$ and $Q$. Then, writing $\mathcal M$ for the tensor product of the pull-back of $\mathcal L_A$ along the first projection with the pull-back of $\mathcal L_B$ along $\varphi$, for every algebraically closed field $k$, every ring homomorphism $sk : S' \to k$ and every $d > 0$ the $k$-dimension of the global sections of $\mathcal M^{\otimes d}$ on the geometric fibre of the second projection determined by $sk$ (the invariant `geomFibreH0Finrank`, with $\mathcal M^{\otimes d}$ built by iterating $-\otimes\mathcal M$ from the monoidal unit) equals $d^{gA}$ times the corresponding dimension for $\mathcal M$.
--
--   This is the Hilbert-polynomial computation $h^0(\mathcal M^{\otimes d}) = d^{g} h^0(\mathcal M)$ for an ample invertible sheaf $\mathcal M$ on a $g$-dimensional abelian variety, here in the relative form where $\mathcal M$ is the tensor product of a projectively embedding bundle on $A$ with the pull-back along a homomorphism $\varphi$ of one on $B$. It supplies the degree pieces used in the quaternionic Hom-scheme statement [`CerednikDrinfeld.QM.exists_representsLatticeActions_of_closedImmersionBySections_of_topologicalKrullDim`](thm.html#CerednikDrinfeld.QM.exists_representsLatticeActions_of_closedImmersionBySections_of_topologicalKrullDim), matching $h^0$ data with Hilbert polynomials $P_e = e\,t^{g}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_geomFibreH0Finrank_tensorPow_eq_pow_mul_of_hom_of_closedImmersionBySections.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open MonoidalCategory

theorem GoodReductionJacobian.RelativeGroupLaw.geomFibreH0Finrank_tensorPow_eq_pow_mul_of_hom_of_closedImmersionBySections
    (S : Type) [CommRing S] {A B : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of S)) (g : B ⟶ Spec (CommRingCat.of S))
    (LA : RelativeGroupLaw S f) (LB : RelativeGroupLaw S g)
    (hAc : LA.IsCommutative) (hBc : LB.IsCommutative)
    (hA : AbelianSchemePropertyBundle S f) (hB : AbelianSchemePropertyBundle S g)
    (𝓛A : A.Modules) (hA₁ : Scheme.Modules.IsInvertible 𝓛A) (hA₂ : Scheme.Modules.ClosedImmersionBySections 𝓛A f)
    (𝓛B : B.Modules) (hB₁ : Scheme.Modules.IsInvertible 𝓛B) (hB₂ : Scheme.Modules.ClosedImmersionBySections 𝓛B g)
    (gA : ℕ) (hdim : ∀ x : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {x}) = gA)
    (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s)
    (hhom : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
        pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ =
          (LB.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (d : ℕ), 0 < d →
      Scheme.Modules.geomFibreH0Finrank (pullback.snd f s)
          (Nat.rec (motive := fun _ => (pullback f s).Modules) (𝟙_ (pullback f s).Modules)
            (fun _ M => M ⊗ ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛A ⊗ (Scheme.Modules.pullback φ).obj 𝓛B)) d) k sk =
        d ^ gA * Scheme.Modules.geomFibreH0Finrank (pullback.snd f s)
          ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛A ⊗ (Scheme.Modules.pullback φ).obj 𝓛B) k sk := by sorry
