-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint
-- name    : ModularCurve.JZeroNeronObjectAtP.frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/ca5a09fb-4fec-509d-8493-2534fba1513d
-- title:
--   Frobenius and Uₚ torus matrices are mutually inverse
-- statement:
--   Fix $N_0 \ge 1$ and a prime $p$ with $p \nmid N_0$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose set of non-units contains the image of $p$ (`A.LiesOverPrime p`), level data $\Lambda$ for $N_0, p, A$ satisfying `Λ.IsJacobian`, and an object $O$ of `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`, the residue field $\kappa_A$ of $A$ having characteristic $p$. The data are: an endomorphism $\Xi_G$ of the fibre product of $O.g$ with $\operatorname{Spec}\kappa_A \to \operatorname{Spec} A \to$ `base p` which commutes with the first projection and which over the base is $\operatorname{Spec}$ of the $p$-power map of $\kappa_A$; an additive endomorphism $P_0$ of $\mathbb{Z}^{O.toricRank}$ such that applying the $p$-power map to coefficients of the group algebra and then $O.torusFibre$ agrees with applying $P_0$ to the grading group, then $O.torusFibre$, then $\Xi_G$; a morphism $\varphi_U : G \to G$ over `base p` additive for the relative group law $O.L$ on all $T$-points; an additive endomorphism $M_0$ of $\mathbb{Z}^{O.toricRank}$ such that $\operatorname{Spec}$ of the domain map induced by $M_0$ followed by $O.torusFibre$ equals $O.torusFibre$ followed by the restriction of $\varphi_U$ to that fibre; and $\varphi \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ lying in the decomposition subgroup of $A$ and acting on $\kappa_A$ as $x \mapsto x^p$. Assume finally that for every prime $\ell \ne p$, every $k$, and every $A$-algebra map $\chi$ from $A[(\mathbb{Z}/\ell^k)^{O.toricRank}]$ to $\overline{\mathbb{Q}}$, the endomorphism $\varphi_U$ carries the point $\varphi \cdot O.\mathrm{toricPoint}(\ell^k,\chi)$ of $J_0(N_0p)$ to $p \cdot O.\mathrm{toricPoint}(\ell^k,\chi)$, and also $\varphi$ carries $\varphi_U$ applied to $O.\mathrm{toricPoint}(\ell^k,\chi)$ to $p \cdot O.\mathrm{toricPoint}(\ell^k,\chi)$. Then $P_0 \circ M_0$ and $M_0 \circ P_0$ are both the identity of $\mathbb{Z}^{O.toricRank}$.
--
--   This is the cancellation, on the character lattice of the maximal torus of the special fibre at $p$, of the Frobenius permutation against the shift induced by the Hecke operator $U_p$: the two integer matrices $P_0$ and $M_0$ attached to these operators are mutually inverse. It feeds into [`ModularCurve.jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_of_isFrobeniusAt_of_bridge`](thm.html#ModularCurve.jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_of_isFrobeniusAt_of_bridge), the step identifying the Frobenius action on the toric part with the $U_p$ eigenvalue in the level-lowering argument at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    [CharP (ResidueField ↥A) p]

    (ΞG : pullback O.g (resPt A ≫ Λ.σA) ⟶ pullback O.g (resPt A ≫ Λ.σA))
    (hΞ₁ : ΞG ≫ pullback.fst _ _ = pullback.fst _ _)
    (hΞ₂ : ΞG ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)))

    (P₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ))
    (hP₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ℤ) (frobenius (ResidueField ↥A) p))) ≫ O.torusFibre.1 =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) P₀)) ≫ O.torusFibre.1 ≫ ΞG)

    (φU : SchemeHomOver O.g O.g)
    (hφUmul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp (O.L.mul s x y) φU =
        O.L.mul s (NeronModelInfra.schemeHomOverComp x φU) (NeronModelInfra.schemeHomOverComp y φU))
    (M₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ))
    (hM₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ O.torusFibre.1 =
      O.torusFibre.1 ≫ (NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) O.g O.g φU).1)

    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ p) (hφD : φ ∈ A.decompositionSubgroup ℚ)

    (hUF : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ (k : ℕ) (hm : 0 < ℓ ^ k) (χ : muCoord ↥A O.toricRank (ℓ ^ k) →ₐ[↥A] AlgebraicClosure ℚ),
      O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts (φ • O.toricPoint (ℓ ^ k) hm χ)) φU) = p • O.toricPoint (ℓ ^ k) hm χ)
    (hFU : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ (k : ℕ) (hm : 0 < ℓ ^ k) (χ : muCoord ↥A O.toricRank (ℓ ^ k) →ₐ[↥A] AlgebraicClosure ℚ),
      φ • O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts (O.toricPoint (ℓ ^ k) hm χ)) φU) = p • O.toricPoint (ℓ ^ k) hm χ) :
    P₀.comp M₀ = AddMonoidHom.id _ ∧ M₀.comp P₀ = AddMonoidHom.id _ := by sorry
