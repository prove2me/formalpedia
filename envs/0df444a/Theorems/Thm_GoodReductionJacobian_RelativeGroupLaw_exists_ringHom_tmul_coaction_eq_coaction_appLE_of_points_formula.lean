-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_ringHom_tmul_coaction_eq_coaction_appLE_of_points_formula
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_ringHom_tmul_coaction_eq_coaction_appLE_of_points_formula
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/07ab177f-e55e-5327-8627-5a57a2ba080d
-- title:
--   Equivariance of the chartwise coaction under (φ,φ^sharp)
-- statement:
--   Let $K$ be a field, $f : A \to \operatorname{Spec} K$ a scheme over $K$, $L$ a relative group law on $f$ (a functorial group structure on the sets $\{\psi : T \to A \mid \psi \circ f = t\}$ of $T$-points over $K$, with multiplication natural in $T$), $n$ a natural number, and $H$ a commutative Hopf algebra over $K$. Assume given, for every $K$-algebra $T$, a bijection $e_T$ from the $K$-algebra homomorphisms $H \to T$, regarded as a monoid under convolution, onto the $n$-torsion subset $\{x : L.\mathrm{nsmul}\,n\,x = L.\mathrm{one}\}$ of the $\operatorname{Spec} T$-points of $A$ over $K$, which is multiplicative (`he_mul`) and natural in $T$ (`he_nat`); a morphism $\mathrm{act} : A \times_{\operatorname{Spec} K} \operatorname{Spec} H \to A$ over $K$ via the first projection (`hact`) pinned on points by $\mathrm{act}(x,\varphi) = L.\mathrm{mul}(x, e_T\varphi)$ (`hpts`); and a morphism $N : A \to A$ over $K$ with $\mathrm{pr}_1 \circ N = \mathrm{act} \circ N$ (`hsh`). Sections of $A$, resp. of the pullback, carry the $K$-algebra structures induced by $f$, resp. $\mathrm{pr}_1$ followed by $f$. Assume further that $N^{-1}U$ is affine for every affine open $U$; that for every affine open $V$ there is a $K$-algebra isomorphism $\varepsilon_V : \Gamma(A\times \operatorname{Spec} H, \mathrm{pr}_1^{-1}V) \cong \Gamma(A,V) \otimes_K H$ sending $\mathrm{pr}_1^*a$ to $a \otimes 1$, sending $\mathrm{pr}_2^*h$ (for $h \in H$ viewed in the global sections of $\operatorname{Spec} H$) to $1 \otimes h$, and compatible with restriction to smaller affine opens; that $\mathrm{pr}_1^{-1}(N^{-1}U) \le \mathrm{act}^{-1}(N^{-1}U)$ for affine $U$; and that $\rho_U : \Gamma(A,N^{-1}U) \to \Gamma(A,N^{-1}U)\otimes_K H$ is the $K$-algebra map obtained by composing the restricted comorphism of $\mathrm{act}$ with $\varepsilon_{N^{-1}U}$. Finally let $\varphi : A \to A$ be a morphism over $K$ which is a homomorphism for $L$ on $T$-points for every base $T \to \operatorname{Spec} K$, commutes with $N$, and is matched through $e$ with a $K$-algebra endomorphism $\varphi^\sharp$ of $H$, in the sense that $e_T(q \circ \varphi^\sharp)$ is $e_T(q)$ followed by $\varphi$. Then for all affine opens $U, W$ with $N^{-1}W \le \varphi^{-1}(N^{-1}U)$ there exists a ring homomorphism $\Xi : \Gamma(A,N^{-1}U)\otimes_K H \to \Gamma(A,N^{-1}W)\otimes_K H$ with $\Xi(s \otimes 1) = \varphi^{*}s \otimes 1$, $\Xi(1 \otimes x) = 1 \otimes \varphi^\sharp x$, and $\Xi(\rho_U s) = \rho_W(\varphi^{*}s)$, where $\varphi^{*}$ denotes the comorphism of $\varphi$ from $N^{-1}U$ to $N^{-1}W$.
--
--   This is the statement that the chartwise coaction of the $n$-torsion group scheme $\operatorname{Spec} H$ on $A$, read off in affine charts $N^{-1}U$ through the Künneth isomorphisms $\varepsilon$, is equivariant for an endomorphism $\varphi$ of the group law together with the Hopf-algebra endomorphism $\varphi^\sharp$ corresponding to it on torsion points. It supplies the equivariance input to [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_ker_d_one_forall_unitPullback_sub_mem_range_of_charP`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_ker_d_one_forall_unitPullback_sub_mem_range_of_charP).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_ringHom_tmul_coaction_eq_coaction_appLE_of_points_formula.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_Dieudonne_ModpRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_ringHom_tmul_coaction_eq_coaction_appLE_of_points_formula
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (n : ℕ)
    (H : Type u) [CommRing H] [HopfAlgebra K H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
        (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1)

    (act : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⟶ A)
    (hact : act ≫ f = (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f)
    (hpts : ∀ (T : Type u) [CommRing T] [Algebra K T]
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) f) (φ : WithConv (H →ₐ[K] T))
        (hx : x.1 ≫ f = Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K H))),
      pullback.lift x.1 (Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T))) hx ≫ act =
        (L.mul (Spec.map (CommRingCat.ofHom (algebraMap K T))) x (e T φ).val).1)
    (N : A ⟶ A) (hN : N ≫ f = f)
    (hsh : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ N = act ≫ N) :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens, Algebra K Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), W) := fun W =>
      Scheme.TwoAffineOpenCover.algebraOfHom ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f) W
    ∀ (hNaff : ∀ U : A.affineOpens, IsAffineOpen (N ⁻¹ᵁ (U : A.Opens)))

    (ε : ∀ (V : A.Opens) (_ : IsAffineOpen V), Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H)
    (hε_fst : ∀ (V : A.Opens) (hV : IsAffineOpen V) (a : Γ(A, V)),
      ε V hV (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app V).hom a) = a ⊗ₜ[K] (1 : H))
    (hε_snd : ∀ (V : A.Opens) (hV : IsAffineOpen V) (h : H),
      ε V hV (((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).appLE ⊤
          ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) = (1 : Γ(A, V)) ⊗ₜ[K] h)
    (hε_res : ∀ (V V' : A.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V)
        (s : Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)),
      Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ε V hV s) =
        ε V' hV' (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).presheaf.map (homOfLE ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).preimage_mono hle)).op).hom s))
    (hle : ∀ U : A.affineOpens, (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens)) ≤ act ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens)))

    (ρ : ∀ U : A.affineOpens, Γ(A, N ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H)
    (hρ : ∀ (U : A.affineOpens) (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
      ρ U s = ε (N ⁻¹ᵁ (U : A.Opens)) (hNaff U) ((act.appLE (N ⁻¹ᵁ (U : A.Opens)) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) (hle U)).hom s))

    (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hφ_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ φ =
        (L.mul t ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩ ⟨Q.1 ≫ φ, by rw [Category.assoc, hφ]; exact Q.2⟩).1)
    (hφN : φ ≫ N = N ≫ φ) (φH : H →ₐ[K] H)
    (hφH : ∀ (T : Type u) [CommRing T] [Algebra K T] (q : WithConv (H →ₐ[K] T)),
      ((e T (.toConv (q.ofConv.comp φH))).val : SchemeHomOver _ f).1 = (e T q).val.1 ≫ φ)
    (U W : A.affineOpens) (hWU : N ⁻¹ᵁ (W : A.Opens) ≤ φ ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))),
    ∃ Ξ : Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H →+* Γ(A, N ⁻¹ᵁ (W : A.Opens)) ⊗[K] H,
      (∀ s : Γ(A, N ⁻¹ᵁ (U : A.Opens)),
          Ξ (s ⊗ₜ[K] (1 : H)) = (φ.appLE (N ⁻¹ᵁ (U : A.Opens)) (N ⁻¹ᵁ (W : A.Opens)) hWU).hom s ⊗ₜ[K] (1 : H)) ∧
      (∀ x : H, Ξ ((1 : Γ(A, N ⁻¹ᵁ (U : A.Opens))) ⊗ₜ[K] x) = (1 : Γ(A, N ⁻¹ᵁ (W : A.Opens))) ⊗ₜ[K] φH x) ∧
      (∀ s : Γ(A, N ⁻¹ᵁ (U : A.Opens)),
          Ξ (ρ U s) = ρ W ((φ.appLE (N ⁻¹ᵁ (U : A.Opens)) (N ⁻¹ᵁ (W : A.Opens)) hWU).hom s)) := by sorry
