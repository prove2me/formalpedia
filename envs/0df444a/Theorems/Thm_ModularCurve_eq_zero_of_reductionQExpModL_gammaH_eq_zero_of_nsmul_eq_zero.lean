-- Prove2me | Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
-- name    : ModularCurve.eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/178fb6e8-e637-5dc7-9c67-417102305391
-- title:
--   Reduction of J_H is injective on prime-to-ℓ torsion
-- statement:
--   Let $M$ be a nonzero natural number, $H \le (\mathbb{Z}/M)^\times$ a subgroup, and let $\Gamma = \Gamma_H(M)$ be [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image under the inclusion $\Gamma_0(M) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ sending $\gamma$ to its lower-right entry modulo $M$. Let $\ell$ be a prime not dividing $M$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `A.LiesOverPrime ℓ`, i.e. the image of $\ell$ lies in the nonunits of $A$; write $k$ for the residue field of $A$. Assume [`ModularCurve.ReductionInputsQExpModL A Γ`](def/ModularCurve_QExpReductionModL.html#L296): the predicates `IsLaurentPlaceReduction` and `LaurentPrincipalGeneratedByIntegral` hold for $A$, the residue map $A \to k$, the field $F_0 =$ `qExpFunctionFieldC ℚ Γ` $\subseteq \mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios `intFormRatiosC` of $q$-expansions attached to $\Gamma$, and its analogue `qExpFunctionFieldC k Γ` $\subseteq k((q))$, for some map $r$ on places. Let $m$ be a natural number not divisible by $\ell$, and let $z$ belong to [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127), the group of degree-zero divisor classes of `xHFunctionFieldBar M H`, the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of $F_0$. If $m \cdot z = 0$ and [`ModularCurve.reductionQExpModL A Γ z = 0`](def/ModularCurve_QExpReductionModL.html#L312), then $z = 0$. (The reduction homomorphism to the degree-zero divisor class group of `qExpFunctionFieldC k Γ` over $k$ is defined by choice from such data, and is zero when no data exists; the hypothesis on $A$ and $\Gamma$ makes it an actual reduction map.)
--
--   This is the injectivity of reduction on torsion of order prime to the residue characteristic, in the form used for the Jacobian $J_H(M)$ of the modular curve $X_H(M)$ at a place of $\overline{\mathbb{Q}}$ above a prime $\ell \nmid M$ — classically due to Deuring and Shimura–Taniyama, and for abelian varieties with good reduction the lemma of Serre and Tate. It is used to show that inertia at $\ell$ acts trivially on the $\ell'$-torsion, and hence in the determination of the Frobenius action on Tate modules of $J_H$ and $J_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (h : ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H))
    (m : ℕ) (hm : ¬ ℓ ∣ m) (z : ModularCurve.JH M H) (hmz : m • z = 0)
    (hz : ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) z = 0) :
    z = 0 := by sorry
