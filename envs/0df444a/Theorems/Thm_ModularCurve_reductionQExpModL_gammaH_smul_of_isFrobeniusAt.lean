-- Prove2me | Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt
-- name    : ModularCurve.reductionQExpModL_gammaH_smul_of_isFrobeniusAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/b76dc063-ead6-52bc-944b-12567e652cd0
-- title:
--   Arithmetic Frobenius reduces to the Frobenius push-forward on J_H
-- statement:
--   Fix $M \ge 1$ (nonzero), a subgroup $H \le (\mathbb{Z}/M)^\times$, and write $\Gamma =$ [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) for the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image of $\Gamma_0(M)$ under its inclusion of the preimage of $H$ under the homomorphism `gamma0Units` that sends $\gamma \in \Gamma_0(M)$ to the unit of $\mathbb{Z}/M$ given by `Gamma0Map M γ` (inverse the class of the upper-left entry). Let $\ell$ be a prime with $\ell \nmid M$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $\ell$ in the sense that $\ell$ is a nonunit of $A$, with residue field $k =$ `IsLocalRing.ResidueField A` of characteristic $\ell$. Assume [`ModularCurve.ReductionInputsQExpModL A Γ`](def/ModularCurve_QExpReductionModL.html#L296), i.e. that `LaurentReductionInputs` holds for $A$, its residue map, the intermediate field $F_0 =$ `qExpFunctionFieldC ℚ Γ` of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios `intFormRatiosC`, and $\bar F =$ `qExpFunctionFieldC k Γ` inside $k((q))$: there is a map $r$ on places which is an `IsLaurentPlaceReduction` and `LaurentPrincipalGeneratedByIntegral` holds. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ which is a Frobenius at $A$ for $\ell$: $\sigma$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on $k$ by $x \mapsto x^{\ell}$. Then for every degree-zero divisor class $z \in J_H(M) = \mathrm{Pic}^0$ of the Laurent base change of $F_0$ to $\overline{\mathbb{Q}}$, the reduction map `reductionQExpModL` sends $\sigma \cdot z$ to `qExpFrobeniusPushforwardModL` applied to the reduction of $z$; the latter is the $\mathrm{Pic}^0$ push-forward along the degree-$\ell$ Frobenius inclusion `qExpFrobeniusModL k Γ ℓ` when `QExpFrobeniusInputsModL k Γ ℓ` holds, and the zero map otherwise.
--
--   This is the compatibility, in Deuring's style, between the Galois action on the Jacobian $J_H(M)$ in characteristic zero and the geometric Frobenius on the reduction of the modular curve at a place above a prime $\ell$ not dividing the level. It is the input for the Eichler–Shimura type Frobenius relations on Tate modules, being cited by [`ModularCurve.frobeniusQuadratic_tateModule_jH`](thm.html#ModularCurve.frobeniusQuadratic_tateModule_jH), [`ModularCurve.frobeniusQuadratic_tateModule_jOne`](thm.html#ModularCurve.frobeniusQuadratic_tateModule_jOne) and the associated statement on $\mathrm{ord}$ of the Frobenius quadratic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.reductionQExpModL_gammaH_smul_of_isFrobeniusAt (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (h : ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ)
    (z : ModularCurve.JH M H) :
    ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) (σ • z) =
      ModularCurve.qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A)
        (CohCarrier.GammaH M H) ℓ
        (ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) z) := by sorry
