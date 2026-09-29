-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_endo_algHom_pinned_unitPullback_of_cls_cup
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_endo_algHom_pinned_unitPullback_of_cls_cup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/3d237ca8-9d02-506f-bab9-759c6b7820c6
-- title:
--   Pinned endomorphism action on Čech algebras of an abelian scheme
-- statement:
--   Let $k$ be a field, $f\colon A\to\operatorname{Spec}k$ a morphism of schemes, $L$ a relative group law for $f$ (functorial group operations on the sets $\{\varphi\colon T\to A\mid \varphi\circ f=t\}$, natural in $T$), and $hA$ the assertion that $f$ is smooth, proper, has connected fibres and admits a relative group law. Let $\mathcal K$ be an ordered affine cover of $A$ (a finite linearly ordered family of affine opens with supremum $\top$) and $\mathcal W$ one of $A\times_{k}A=\mathrm{pullback}\,f\,f$, together with index maps $\mathrm{lam}_1,\mathrm{lam}_2$ and hypotheses $h_1,h_2$ that each $\mathcal W$-open lies in the preimage under the first, respectively second, projection of the corresponding $\mathcal K$-open. Next, a $k$-algebra $H$ with a graded-monoid family of $k$-submodules $\mathcal A_n$ and $k$-linear class maps $\mathrm{cls}_n$ from the $n$-cocycles of the Čech complex of the presheaf `OModulePresheaf.unit f` (sections of $\mathcal O_A$, with restriction maps) on $\mathcal K$ into $H$, such that the range of $\mathrm{cls}_n$ is $\mathcal A_n$, the $\mathcal A_n$ decompose $H$ internally as a direct sum, $\mathrm{cls}_0$ is injective, $\mathrm{cls}_{n+1}$ vanishes exactly on coboundaries, $\mathrm{cls}$ carries the Čech cup product to multiplication in $H$, and the cochain constantly $1$ on every intersection is a $0$-cocycle with class $1$. The same data $(H',\mathcal A'_n,\mathrm{cls}'_n)$ is given for $A\times_kA$ over $k$ with cover $\mathcal W$, except for a unit clause. Finally, $p_1,p_2\colon H\to H'$ are $k$-algebra maps such that for every $n$ and every $n$-cocycle $z$ on $\mathcal K$ the pullbacks of $z$ to $\mathcal W$ along the two projections (via `OModulePresheaf.unitPullback` with $\mathrm{lam}_1,h_1$ and $\mathrm{lam}_2,h_2$) are again cocycles, with $p_1(\mathrm{cls}_n z)$ and $p_2(\mathrm{cls}_n z)$ equal to their classes. The conclusion asserts the existence of $k$-algebra endomorphisms $\rho(\varphi,h_\varphi)$ of $H$ and $\rho_1(\varphi,h_\varphi),\rho_2(\varphi,h_\varphi)$ of $H'$, indexed by the morphisms $\varphi\colon A\to A$ with $\varphi$ followed by $f$ equal to $f$, such that: each $\rho(\varphi)$ maps $\mathcal A_n$ into $\mathcal A_n$; $\rho(\mathrm{id}_A)$ is the identity; $\rho(\varphi$ followed by $\psi)=\rho(\varphi)\circ\rho(\psi)$; if $\chi$ is the pointwise $L$-sum of $\varphi$ and $\psi$, meaning that for every $t\colon T\to\operatorname{Spec}k$ and every $T$-point $P$ over $t$ one has $P$ followed by $\chi$ equal to the underlying morphism of $L.\mathrm{mul}$ applied to $P\circ\varphi$ and $P\circ\psi$, then $\rho(\chi)$ agrees with $\rho(\varphi)+\rho(\psi)$ on $\mathcal A_1$; $\rho(\varphi)$ is pinned to pullback of cochains, namely for any ordered affine cover $\mathcal V$ of $A$ with index maps refining $\mathcal K$ along $\varphi$ and along $\mathrm{id}_A$, and any $(n+1)$-cocycles $z,z'$ on $\mathcal K$ whose pullbacks to $\mathcal V$ along $\varphi$ and along $\mathrm{id}_A$ differ by a coboundary, one has $\rho(\varphi)(\mathrm{cls}_{n+1}z)=\mathrm{cls}_{n+1}z'$; the four intertwining relations $\rho_1(\varphi)\circ p_1=p_1\circ\rho(\varphi)$, $\rho_1(\varphi)\circ p_2=p_2$, $\rho_2(\varphi)\circ p_1=p_1$, $\rho_2(\varphi)\circ p_2=p_2\circ\rho(\varphi)$ hold pointwise on $H$; and $\rho_1(\varphi)$, respectively $\rho_2(\varphi)$, satisfy the analogous pinning on $H'$ with $\varphi$ replaced by the morphism of $A\times_kA$ induced by $(\varphi,\mathrm{id})$, respectively $(\mathrm{id},\varphi)$, given as the pullback lift of the two projections with $\varphi$ inserted in one factor.
--
--   This packages the contravariant functoriality of Čech cohomology of the structure sheaf under endomorphisms of an abelian scheme $A$ over a field, together with the compatible actions of $\varphi\times 1$ and $1\times\varphi$ on $A\times_k A$, as degree-preserving algebra endomorphisms of abstract graded Čech-ring handles whose values on classes are determined by cochain pullback. It is used in the construction of the Hopf-algebra/Künneth package for the Čech ring of $\mathcal O_A$ and in the derivation of the induced linear action on degree-one classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_endo_algHom_pinned_unitPullback_of_cls_cup.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct DirectSum

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_endo_algHom_pinned_unitPullback_of_cls_cup
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (𝒦 : A.OrderedAffineCover)
    (𝒲 : (pullback f f).OrderedAffineCover) (lam₁ lam₂ : 𝒲.ι → 𝒦.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst f f ⁻¹ᵁ 𝒦.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd f f ⁻¹ᵁ 𝒦.U (lam₂ w))

    (H : Type u) [Ring H] [Algebra k H] (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜]
    (cls : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n)) →ₗ[k] H)
    (hrange : ∀ n : ℕ, LinearMap.range (cls n) = 𝒜 n) (hint : DirectSum.IsInternal 𝒜)
    (hcls0 : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 0)), cls 0 z = 0 ↔ z = 0)
    (hcls : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 (n + 1)))),
      cls (n + 1) z = 0 ↔
        (z : (OModulePresheaf.unit f).cochain 𝒦 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒦 n))
    (hmul : ∀ (a b : ℕ) (α : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 a)))
        (β : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 b))),
      ∃ hγ : (OModulePresheaf.unit f).cup 𝒦 a b (a + b) rfl α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 (a + b)),
        cls (a + b) ⟨_, hγ⟩ = cls a α * cls b β)
    (hone : ∃ h1 : (fun s => (1 : Γ(A, 𝒦.inter s))) ∈ LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 0),
      cls 0 ⟨fun s => (1 : Γ(A, 𝒦.inter s)), h1⟩ = 1)

    (H' : Type u) [Ring H'] [Algebra k H'] (𝒜' : ℕ → Submodule k H') [SetLike.GradedMonoid 𝒜']
    (cls' : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n)) →ₗ[k] H')
    (hrange' : ∀ n : ℕ, LinearMap.range (cls' n) = 𝒜' n) (hint' : DirectSum.IsInternal 𝒜')
    (hcls'0 : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 0)), cls' 0 z = 0 ↔ z = 0)
    (hcls' : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 (n + 1)))),
      cls' (n + 1) z = 0 ↔
        (z : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 (n + 1)) ∈
          LinearMap.range ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n))
    (hmul' : ∀ (a b : ℕ) (α : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 a)))
        (β : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 b))),
      ∃ hγ : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cup 𝒲 a b (a + b) rfl α.1 β.1 ∈
          LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 (a + b)),
        cls' (a + b) ⟨_, hγ⟩ = cls' a α * cls' b β)
    (p₁ p₂ : H →ₐ[k] H')
    (hp : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n))),
      ∃ (hz₁ : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lam₁ h₁ n z.1 ∈
            LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n))
        (hz₂ : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lam₂ h₂ n z.1 ∈
            LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n)),
        p₁ (cls n z) = cls' n ⟨_, hz₁⟩ ∧ p₂ (cls n z) = cls' n ⟨_, hz₂⟩) :
    ∃ (ρ : ∀ φ : A ⟶ A, φ ≫ f = f → (H →ₐ[k] H))
      (ρ₁ ρ₂ : ∀ φ : A ⟶ A, φ ≫ f = f → (H' →ₐ[k] H')),
      (∀ (φ : A ⟶ A) (hφ : φ ≫ f = f) (n : ℕ), ∀ x ∈ 𝒜 n, ρ φ hφ x ∈ 𝒜 n) ∧
      (ρ (𝟙 A) (Category.id_comp f) = AlgHom.id k H) ∧
      (∀ (φ ψ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f),
        ρ (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) = (ρ φ hφ).comp (ρ ψ hψ)) ∧
      (∀ (φ ψ χ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f) (hχ : χ ≫ f = f),
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
            P.1 ≫ χ = (L.mul t ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩
              ⟨P.1 ≫ ψ, by rw [Category.assoc, hψ]; exact P.2⟩).1) →
        ∀ x ∈ 𝒜 1, ρ χ hχ x = ρ φ hφ x + ρ ψ hψ x) ∧
      (∀ (φ : A ⟶ A) (hφ : φ ≫ f = f) (𝒱 : A.OrderedAffineCover) (lam lam' : 𝒱.ι → 𝒦.ι)
          (hl : ∀ v, 𝒱.U v ≤ φ ⁻¹ᵁ 𝒦.U (lam v)) (hl' : ∀ v, 𝒱.U v ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam' v))
          (n : ℕ) (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 (n + 1)))),
          OModulePresheaf.unitPullback (πX := f) φ 𝒱 𝒦 lam hl (n + 1) z.1 -
              OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 𝒦 lam' hl' (n + 1) z'.1 ∈
            LinearMap.range ((OModulePresheaf.unit f).d 𝒱 n) →
          ρ φ hφ (cls (n + 1) z) = cls (n + 1) z') ∧
      (∀ (φ : A ⟶ A) (hφ : φ ≫ f = f) (x : H),
          ρ₁ φ hφ (p₁ x) = p₁ (ρ φ hφ x) ∧ ρ₁ φ hφ (p₂ x) = p₂ x ∧
          ρ₂ φ hφ (p₁ x) = p₁ x ∧ ρ₂ φ hφ (p₂ x) = p₂ (ρ φ hφ x)) ∧
      (∀ (φ : A ⟶ A) (hφ : φ ≫ f = f) (𝒱 : (pullback f f).OrderedAffineCover) (lam lam' : 𝒱.ι → 𝒲.ι)
          (hl : ∀ v, 𝒱.U v ≤
            (pullback.lift (pullback.fst f f ≫ φ) (pullback.snd f f)
              (by rw [Category.assoc, hφ]; exact pullback.condition)) ⁻¹ᵁ 𝒲.U (lam v))
          (hl' : ∀ v, 𝒱.U v ≤ (𝟙 (pullback f f)) ⁻¹ᵁ 𝒲.U (lam' v))
          (n : ℕ) (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 (n + 1)))),
          OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f)
                (pullback.lift (pullback.fst f f ≫ φ) (pullback.snd f f)
                  (by rw [Category.assoc, hφ]; exact pullback.condition)) 𝒱 𝒲 lam hl (n + 1) z.1 -
              OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (𝟙 (pullback f f)) 𝒱 𝒲 lam' hl' (n + 1) z'.1 ∈
            LinearMap.range ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒱 n) →
          ρ₁ φ hφ (cls' (n + 1) z) = cls' (n + 1) z') ∧
      (∀ (φ : A ⟶ A) (hφ : φ ≫ f = f) (𝒱 : (pullback f f).OrderedAffineCover) (lam lam' : 𝒱.ι → 𝒲.ι)
          (hl : ∀ v, 𝒱.U v ≤
            (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ φ)
              (by rw [Category.assoc, hφ]; exact pullback.condition.trans rfl)) ⁻¹ᵁ 𝒲.U (lam v))
          (hl' : ∀ v, 𝒱.U v ≤ (𝟙 (pullback f f)) ⁻¹ᵁ 𝒲.U (lam' v))
          (n : ℕ) (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 (n + 1)))),
          OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f)
                (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ φ)
                  (by rw [Category.assoc, hφ]; exact pullback.condition.trans rfl)) 𝒱 𝒲 lam hl (n + 1) z.1 -
              OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (𝟙 (pullback f f)) 𝒱 𝒲 lam' hl' (n + 1) z'.1 ∈
            LinearMap.range ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒱 n) →
          ρ₂ φ hφ (cls' (n + 1) z) = cls' (n + 1) z') := by sorry
