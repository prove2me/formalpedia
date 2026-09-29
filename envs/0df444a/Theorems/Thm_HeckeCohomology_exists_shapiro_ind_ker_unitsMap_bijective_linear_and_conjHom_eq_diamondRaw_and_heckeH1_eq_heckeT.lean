-- Prove2me | Theorems.Thm_HeckeCohomology_exists_shapiro_ind_ker_unitsMap_bijective_linear_and_conjHom_eq_diamondRaw_and_heckeH1_eq_heckeT
-- name    : HeckeCohomology.exists_shapiro_ind_ker_unitsMap_bijective_linear_and_conjHom_eq_diamondRaw_and_heckeH1_eq_heckeT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/47da3641-1285-57bf-a6ed-467d3747ae20
-- title:
--   Shapiro isomorphism for P¹(𝔽_q), with diamond and Hecke compatibility
-- statement:
--   Let $N\ge 1$, let $q$ be a prime with $q\nmid N$, and let $\kappa$ be a field. Let $\mathrm{lift}\colon\Gamma_0(Nq)\to\Gamma_0(N)$ be any function preserving the underlying matrix in $\mathrm{SL}_2(\mathbb{Z})$. Write $A$ for the representation of $\Gamma_{\perp}(N)$ — the image in $\mathrm{SL}_2(\mathbb{Z})$ of the matrices of $\Gamma_0(N)$ whose lower-right entry is trivial in $(\mathbb{Z}/N)^\times$ — on the finitely supported $\kappa$-valued functions on $\mathbb{P}^1(\mathbb{F}_q)$, obtained from the permutation representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ by reducing matrices modulo $q$. Then there is an additive map $\Phi$ from $H^1(\Gamma_\perp(N),A)$ to the group of $\kappa$-valued additive characters of $\Gamma_{H}(Nq)$, $H=\ker\bigl((\mathbb{Z}/Nq)^\times\to(\mathbb{Z}/N)^\times\bigr)$, such that: $\Phi$ is bijective; $\Phi(c\cdot x)=c\cdot\Phi(x)$ for $c\in\kappa$; for every $\sigma\in\Gamma_0(Nq)$ and every morphism $c$ from the $\mathrm{lift}(\sigma)$-conjugate of $A$ to $A$ acting as the inverse of the reduction of $\mathrm{lift}(\sigma)$ mod $q$, $\Phi$ intertwines the degree-one map induced by conjugation by $\mathrm{lift}(\sigma)$ together with $c$ with the operator $\varphi\mapsto\varphi\circ(\text{conjugation by }\sigma)$; and for every prime $\ell\nmid Nq$ and unit $u\in(\mathbb{Z}/q)^\times$ with $u=\ell$, given any proof that the action of $\mathrm{diag}(u,1)$ on $A$ is a twist relative to $\mathrm{cTop}\,N\,\perp\,\ell$ (the upper-triangular conjugation map $\Gamma_\perp(N)\cap\Gamma_0^{\mathrm{up}}(\ell)\to\Gamma_\perp(N)$ corestricted to $\top$), $\Phi$ carries the corresponding transfer Hecke operator on $H^1(A)$ to the transfer operator $T_\ell$ on characters of $\Gamma_H(Nq)$.
--
--   This is the Shapiro (induction) comparison between the first cohomology of $\Gamma_1(N)$ with coefficients in the permutation module of $\mathbb{P}^1(\mathbb{F}_q)$ and the first cohomology of $\Gamma_1(N)\cap\Gamma_0(q)$ with trivial coefficients, packaged together with the equivariance for diamond and Hecke operators away from $Nq$. It is used in the analysis of eigensystems on $H^1$ at level $Nq$, where the Steinberg quotient and Eisenstein alternatives are separated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCohomology_exists_shapiro_ind_ker_unitsMap_bijective_linear_and_conjHom_eq_diamondRaw_and_heckeH1_eq_heckeT.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_DClassCoeff
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem
HeckeCohomology.exists_shapiro_ind_ker_unitsMap_bijective_linear_and_conjHom_eq_diamondRaw_and_heckeH1_eq_heckeT
    (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime] (hqN : ¬ q ∣ N) (κ : Type) [Field κ]
    (lift : CongruenceSubgroup.Gamma0 (N * q) → CongruenceSubgroup.Gamma0 N)
    (hlift : ∀ σ, ((lift σ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
      (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    ∃ Φ : groupCohomology.H1
        (Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
          ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (CohCarrier.GammaH N ⊥).subtype)))) →+
        CohCarrier.H1 (N * q) (ZMod.unitsMap (dvd_mul_right N q)).ker κ,
      Function.Bijective Φ ∧
      (∀ (c : κ) x, Φ (c • x) = c • Φ x) ∧
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
