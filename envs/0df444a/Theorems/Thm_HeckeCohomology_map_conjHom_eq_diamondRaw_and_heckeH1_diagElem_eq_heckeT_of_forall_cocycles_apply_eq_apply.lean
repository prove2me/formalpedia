-- Prove2me | Theorems.Thm_HeckeCohomology_map_conjHom_eq_diamondRaw_and_heckeH1_diagElem_eq_heckeT_of_forall_cocycles_apply_eq_apply
-- name    : HeckeCohomology.map_conjHom_eq_diamondRaw_and_heckeH1_diagElem_eq_heckeT_of_forall_cocycles_apply_eq_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/e7f95669-0d8d-5cc0-a862-ba7f28d69fea
-- title:
--   Evaluation at a fixed point respects diamonds and Hecke operators
-- statement:
--   Fix $N\ge 1$, a prime $q$ with $q\nmid N$, and a field $\kappa$. Write $\Gamma_\bot(N)\subset SL_2(\mathbb Z)$ for the subgroup of elements of $\Gamma_0(N)$ whose associated unit mod $N$ is trivial, and $V$ for the permutation representation of $GL_2(\mathbb Z/q)$ on finitely supported $\kappa$-valued functions on $\mathbb P^1(\mathbb Z/q)$, viewed as a representation of $\Gamma_\bot(N)$ via reduction mod $q$; let $H=\ker\big((\mathbb Z/Nq)^\times\to(\mathbb Z/N)^\times\big)$ and let $\mathrm{H1}(Nq,H,\kappa)$ be the group of additive homomorphisms from the additivisation of $\Gamma_H(Nq)$ to $\kappa$. Assume given a map $\mathrm{lift}:\Gamma_0(Nq)\to\Gamma_0(N)$ preserving the underlying integral matrix, an additive map $\Phi:H^1(\Gamma_\bot(N),V)\to \mathrm{H1}(Nq,H,\kappa)$, and a point $x_0\in\mathbb P^1(\mathbb Z/q)$ fixed by the mod-$q$ reduction of every element of $\Gamma_H(Nq)$, such that for every $1$-cocycle $f$ and every $\gamma\in\Gamma_H(Nq)$ lying in $\Gamma_\bot(N)$ one has $\Phi([f])(\gamma)=f(\gamma)(x_0)$. Then: (1) for each $\sigma\in\Gamma_0(Nq)$ and each morphism $c$ from the restriction of $V$ along $\gamma\mapsto \mathrm{lift}(\sigma)\gamma\,\mathrm{lift}(\sigma)^{-1}$ to $V$ whose underlying map is the inverse action of the mod-$q$ reduction of $\mathrm{lift}(\sigma)$, the degree-one cohomology map induced by this conjugation and $c$ is carried by $\Phi$ to precomposition with conjugation by $\sigma$ on $\mathrm{H1}(Nq,H,\kappa)$; (2) for every prime $\ell\nmid Nq$ (nonzero in the relevant sense) and every unit $u$ of $\mathbb Z/q$ with $u=\ell$, if the permutation action of $\mathrm{diag}(u,1)$ on $V$ is a twist for the map `cTop` from $\Gamma_\bot(N)\cap\Gamma_0^{\mathrm{up}}(\ell)$ into $\Gamma_\bot(N)$ (given by conjugation `conjL`), then $\Phi$ intertwines the associated $H^1$-Hecke operator with the transfer operator `heckeT` at $\ell$ on $\mathrm{H1}(Nq,H,\kappa)$.
--
--   This is the equivariance half of the Shapiro-type comparison between $H^1$ of $\Gamma_1(N)$ with coefficients in the permutation module of $\mathbb P^1(\mathbb F_q)$ and $H^1$ of $\Gamma_1(N)\cap\Gamma_0(q)$ with trivial coefficients, used in the level-raising step at the auxiliary prime $q$. It is invoked by the existence statement that produces such an evaluation map together with its bijectivity, linearity and compatibility with diamond and Hecke operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCohomology_map_conjHom_eq_diamondRaw_and_heckeH1_diagElem_eq_heckeT_of_forall_cocycles_apply_eq_apply.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_DClassCoeff
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped CuspidalType in

theorem
HeckeCohomology.map_conjHom_eq_diamondRaw_and_heckeH1_diagElem_eq_heckeT_of_forall_cocycles_apply_eq_apply
    (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime] (hqN : ¬ q ∣ N) (κ : Type) [Field κ]
    (lift : CongruenceSubgroup.Gamma0 (N * q) → CongruenceSubgroup.Gamma0 N)
    (hlift : ∀ σ, ((lift σ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
      (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (Φ : groupCohomology.H1
        (Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
          ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (CohCarrier.GammaH N ⊥).subtype)))) →+
        CohCarrier.H1 (N * q) (ZMod.unitsMap (dvd_mul_right N q)).ker κ)
    (x₀ : CuspidalType.ProjLine q)
    (hstab :
      (∀ γ : ↥(CohCarrier.GammaH (N * q) (ZMod.unitsMap (dvd_mul_right N q)).ker),
        Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))
          (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) • x₀ = x₀))
    (hval :
      ∀ (f : groupCohomology.cocycles₁
            (Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (CohCarrier.GammaH N ⊥).subtype)))))
        (γ : ↥(CohCarrier.GammaH (N * q) (ZMod.unitsMap (dvd_mul_right N q)).ker))
        (h : (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ CohCarrier.GammaH N ⊥),
        Φ (groupCohomology.H1π
            (Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (CohCarrier.GammaH N ⊥).subtype))))
          f) (Additive.ofMul γ) =
          (f ⟨(γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), h⟩ : CuspidalType.ProjLine q →₀ κ) x₀) :
      (∀ (σ : CongruenceSubgroup.Gamma0 (N * q))
          (c : Rep.res (CohCarrier.conjHom N ⊥ (lift σ))
              (Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
                ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp
                  (CohCarrier.GammaH N ⊥).subtype)))) ⟶
            Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (CohCarrier.GammaH N ⊥).subtype)))),
        (∀ v, c.hom v =
          CuspidalType.ind q κ
            (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))
              (lift σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)))⁻¹ v) →
        ∀ x, Φ (groupCohomology.map (CohCarrier.conjHom N ⊥ (lift σ)) c 1 x) =
          CohCarrier.diamondRaw (N * q) (ZMod.unitsMap (dvd_mul_right N q)).ker κ σ (Φ x)) ∧
      ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q → ∀ (u : (ZMod q)ˣ), (u : ZMod q) = ℓ →
        ∀ (hφ : HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ)
            (Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (CohCarrier.GammaH N ⊥).subtype))))
            (CuspidalType.ind q κ (CuspidalType.diagElem q u)))
          (x : groupCohomology.H1
            (Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (CohCarrier.GammaH N ⊥).subtype))))),
          Φ (HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) _ _ hφ x) =
            CohCarrier.heckeT (N * q) (ZMod.unitsMap (dvd_mul_right N q)).ker ℓ κ (Φ x) := by sorry
