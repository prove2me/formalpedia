-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_product_local_lifts_of_local_lifts
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_product_local_lifts_of_local_lifts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/373cf5da-0c44-57ee-af0a-b1d0fcd5a92f
-- title:
--   Product local lifts over T' for A₀×_T A₀
-- statement:
--   Let $T'$ be a commutative local Artinian ring, $T$ a commutative ring and $\pi\colon T'\to T$ a surjective ring homomorphism whose kernel is a nilpotent ideal. Let $f_0\colon A_0\to\operatorname{Spec}T$ be separated and smooth, equipped with a relative group law $L_0$, i.e. a group structure on the sets $\{\varphi\colon S\to A_0\mid \varphi\circ f_0 = t\}$ for every $t\colon S\to \operatorname{Spec}T$, natural in $(S,t)$. Let $\rho\colon T\to \kappa(T')$ satisfy $\rho\circ\pi=$ the residue map of $T'$. Let $\mathcal U$ be an ordered affine cover of $A_0$ (a finite linearly ordered family of affine opens with supremum $\top$), and for each index $a$ let $q_a\colon Y_a\to\operatorname{Spec}T'$ be smooth with $g_a\colon \mathcal U_a\to Y_a$ making $\mathcal U_a$ the base change of $Y_a$ along $\operatorname{Spec}\pi$. Let $f_k\colon A_k\to\operatorname{Spec}\kappa(T')$ be separated with a relative group law $L_k$, and $i_0\colon A_k\to A_0$ an affine morphism exhibiting $A_k$ as the base change of $A_0$ along $\operatorname{Spec}\rho$, such that $i_0$ carries $L_k$-products to $L_0$-products of the pushed-forward points (hypothesis `hLk`). Finally let $\mathcal W$ be an ordered affine cover of $A_k\times_{\kappa(T')}A_k$ and $\lambda_1,\lambda_2,\lambda_3\colon\mathcal W.\iota\to\mathcal U.\iota$ index maps with $\mathcal W_w$ contained in $p_1^{-1}i_0^{-1}\mathcal U_{\lambda_1w}$, in $p_2^{-1}i_0^{-1}\mathcal U_{\lambda_2w}$ and in $\mu_k^{-1}i_0^{-1}\mathcal U_{\lambda_3w}$, where $\mu_k$ is the $L_k$-product of the two projections. The conclusion asserts: the canonical morphism $j_P\colon A_k\times A_k\to A_0\times_T A_0$ induced by $p_1\circ i_0$ and $p_2\circ i_0$ is affine and exhibits the source as the base change of $A_0\times_T A_0$ along $\operatorname{Spec}\rho$; there are opens $V_w\subseteq A_0\times_T A_0$, affine, with $\bigsqcup_w V_w=\top$ and $j_P^{-1}V_w=\mathcal W_w$, satisfying $V_w\le p_1^{-1}\mathcal U_{\lambda_1w}$, $V_w\le p_2^{-1}\mathcal U_{\lambda_2w}$ and $V_w\le m_0^{-1}\mathcal U_{\lambda_3w}$ for $m_0$ the $L_0$-product of the two projections; affine schemes $Z_w$ with smooth $q_w^Z\colon Z_w\to\operatorname{Spec}T'$ and $g^Z_w\colon V_w\to Z_w$ making $V_w$ the base change of $Z_w$ along $\operatorname{Spec}\pi$ (relative to $V_w\hookrightarrow A_0\times_TA_0\xrightarrow{p_1}A_0\to\operatorname{Spec}T$); and morphisms $h^{(i)}_w\colon Z_w\to Y_{\lambda_iw}$ ($i=1,2,3$) over $\operatorname{Spec}T'$, each lifting the corresponding restriction of $p_1$, $p_2$, $m_0$, in the sense that $g^Z_w$ followed by $h^{(i)}_w$ agrees with the restricted projection (respectively restricted multiplication) $V_w\to\mathcal U_{\lambda_iw}$ followed by $g_{\lambda_iw}$.
--
--   This assembles, on the product $A_0\times_T A_0$, the local data needed to compare smooth lifts over $T'$ of the multiplication and of the two projections: a finite affine cover compatible with the chosen cover of the special fibre's product, smooth affine lifts of its members, and lifted chart morphisms in the three relevant directions. It is used in the construction of the two-cocycle measuring the obstruction to lifting the group law along $\operatorname{Spec}T\hookrightarrow\operatorname{Spec}T'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_product_local_lifts_of_local_lifts.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing Scheme.TwoAffineOpenCover

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_product_local_lifts_of_local_lifts
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀] [Smooth f₀]
    (L₀ : RelativeGroupLaw T f₀)
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')

    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fk]
    (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) [IsAffineHom i₀] (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (hLk : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t fk),
      (Lk.mul t P Q).1 ≫ i₀ =
        (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom ρ))
          ⟨P.1 ≫ i₀, by rw [Category.assoc, hi₀.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ i₀, by rw [Category.assoc, hi₀.w, ← Category.assoc, Q.2]⟩).1)
    (𝒲 : (pullback fk fk).OrderedAffineCover) (lam₁ lam₂ lam₃ : 𝒲.ι → 𝒰.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst fk fk ⁻¹ᵁ (𝒰.comap i₀).U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd fk fk ⁻¹ᵁ (𝒰.comap i₀).U (lam₂ w))
    (h₃ : ∀ w, 𝒲.U w ≤ (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).1 ⁻¹ᵁ (𝒰.comap i₀).U (lam₃ w)) :
    ∃
      (_ : IsAffineHom (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])))
      (_ : IsPullback (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition]))
            (pullback.fst fk fk ≫ fk) (pullback.fst f₀ f₀ ≫ f₀) (Spec.map (CommRingCat.ofHom ρ)))

      (Vop : 𝒲.ι → (pullback f₀ f₀).Opens) (_ : ∀ w, IsAffineOpen (Vop w)) (_ : ⨆ w, Vop w = ⊤)
      (_ : ∀ w, (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ⁻¹ᵁ (Vop w) = 𝒲.U w)
      (hV₁ : ∀ w, Vop w ≤ pullback.fst f₀ f₀ ⁻¹ᵁ 𝒰.U (lam₁ w))
      (hV₂ : ∀ w, Vop w ≤ pullback.snd f₀ f₀ ⁻¹ᵁ 𝒰.U (lam₂ w))
      (hV₃ : ∀ w, Vop w ≤ (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ⁻¹ᵁ 𝒰.U (lam₃ w))

      (Z : 𝒲.ι → Scheme.{u}) (qZ : ∀ w, Z w ⟶ Spec (CommRingCat.of T')) (_ : ∀ w, IsAffine (Z w)) (_ : ∀ w, Smooth (qZ w))
      (gZ : ∀ w, (↑(Vop w) : Scheme.{u}) ⟶ Z w)
      (_ : ∀ w, IsPullback (gZ w) ((Vop w).ι ≫ pullback.fst f₀ f₀ ≫ f₀) (qZ w) (Spec.map (CommRingCat.ofHom π)))

      (hZ₁ : ∀ w, Z w ⟶ Y (lam₁ w)) (hZ₂ : ∀ w, Z w ⟶ Y (lam₂ w)) (hZ₃ : ∀ w, Z w ⟶ Y (lam₃ w)),
      (∀ w, hZ₁ w ≫ q (lam₁ w) = qZ w ∧ gZ w ≫ hZ₁ w = (pullback f₀ f₀).homOfLE (hV₁ w) ≫ (pullback.fst f₀ f₀ ∣_ 𝒰.U (lam₁ w)) ≫ g (lam₁ w)) ∧
      (∀ w, hZ₂ w ≫ q (lam₂ w) = qZ w ∧ gZ w ≫ hZ₂ w = (pullback f₀ f₀).homOfLE (hV₂ w) ≫ (pullback.snd f₀ f₀ ∣_ 𝒰.U (lam₂ w)) ≫ g (lam₂ w)) ∧
      (∀ w, hZ₃ w ≫ q (lam₃ w) = qZ w ∧
        gZ w ≫ hZ₃ w = (pullback f₀ f₀).homOfLE (hV₃ w) ≫ ((L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ∣_ 𝒰.U (lam₃ w)) ≫ g (lam₃ w)) := by sorry
