-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/cef22c1c-8c04-5ba0-8dc0-d95004a018c5
-- title:
--   Semilinear twist of the toric part of the special fibre
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$ and $p$ prime, and assume $p \nmid N_0$. Let $A$ be a valuation subring of an algebraic closure of $\mathbb{Q}$ lying over $p$, in the sense that $p$ belongs to the nonunits of $A$, write $\kappa = \mathrm{ResidueField}\,A$ for its residue field and $\mathrm{resPt}\,A : \operatorname{Spec}\kappa \to \operatorname{Spec} A$ for the morphism induced by the residue map. Let $\Lambda$ be a `LevelData` for $N_0$, $p$, $A$ (a scheme $X$ over `base p` with a relative group law, parametrisations of the generic and residual points of $J_0(N_0)$, and a section $\sigma_A : \operatorname{Spec} A \to$ `base p` restricting to the generic point) satisfying $\Lambda$`.IsJacobian`, and let $O$ be a `JZeroNeronObjectAtP` for these data, with structural morphism $O.g$ and toric rank $t = O$`.toricRank`. Let $\psi$ be a ring automorphism of $\kappa$, and let $\Xi_G$ be an endomorphism of the fibre product of $O.g$ with $\mathrm{resPt}\,A$ followed by $\Lambda.\sigma_A$ which is the identity in the first projection and acts as $\operatorname{Spec}\psi$ in the second, i.e. $\Xi_G$ followed by `pullback.fst` is `pullback.fst`, and $\Xi_G$ followed by `pullback.snd` is `pullback.snd` followed by $\operatorname{Spec}\psi$. Then there is an additive homomorphism $P_0 : \mathbb{Z}^t \to \mathbb{Z}^t$ (for $\mathbb{Z}^t = (\mathrm{Fin}\,t \to \mathbb{Z})$) such that, for the morphism $O$`.torusFibre.1` out of $\operatorname{Spec}$ of the group algebra $\kappa[\mathbb{Z}^t]$ into that fibre product, the morphism induced by applying $\psi$ to coefficients, followed by $O$`.torusFibre.1`, equals the morphism induced by $P_0$ on the group $\mathbb{Z}^t$, followed by $O$`.torusFibre.1` and then by $\Xi_G$.
--
--   This is a rigidity statement for groups of multiplicative type: a $\psi$-semilinear automorphism of the geometric special fibre restricts on its split toric part to the twist by an integral endomorphism of the character lattice $\mathbb{Z}^t$. It is used, with $\psi$ a Frobenius automorphism of the residue field, in the identification of the Frobenius action with $U_p$ on the toric lattice at $p$, through [`ModularCurve.jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_of_isFrobeniusAt_of_bridge`](thm.html#ModularCurve.jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_of_isFrobeniusAt_of_bridge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (ψ : ResidueField ↥A ≃+* ResidueField ↥A)

    (ΞG : pullback O.g (resPt A ≫ Λ.σA) ⟶ pullback O.g (resPt A ≫ Λ.σA))
    (hΞ₁ : ΞG ≫ pullback.fst _ _ = pullback.fst _ _)
    (hΞ₂ : ΞG ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)) :
    ∃ P₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ℤ) ψ.toRingHom)) ≫ O.torusFibre.1 =
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) P₀)) ≫ O.torusFibre.1 ≫ ΞG := by sorry
