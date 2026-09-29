-- Prove2me | Theorems.Thm_ModularCurve_surjOn_reductionQExpModL_gammaH_torsion_pow
-- name    : ModularCurve.surjOn_reductionQExpModL_gammaH_torsion_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/0eaa1522-d35a-5d76-84c7-f18c05f3f0e5
-- title:
--   Surjectivity of reduction on ℓ^k-torsion of J_H(M)
-- statement:
--   Fix a nonzero natural number $M$ and a subgroup $H \le (\mathbb{Z}/M)^\times$, and let $\Gamma = \Gamma_H(M)$ be the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image, under the inclusion of $\Gamma_0(M)$, of the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ sending $\gamma$ to its lower-right entry modulo $M$. Let $\ell$ be a prime with $\ell \nmid M$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime ℓ`, i.e. $\ell$ is a nonunit of $A$; write $k_A$ for its residue field. Assume the hypothesis `ReductionInputsQExpModL`: there exists a map $r$ on places which is a Laurent place reduction for $A$, the residue map $A \to k_A$, the field $F = \mathbb{Q}(\text{intFormRatiosC}\ \mathbb{Q}\ \Gamma) \subseteq \mathbb{Q}((q))$ and the field $\bar F = k_A(\text{intFormRatiosC}\ k_A\ \Gamma) \subseteq k_A((q))$, and the condition `LaurentPrincipalGeneratedByIntegral` holds for these data. Let $k$ be a natural number. Then the reduction homomorphism $\mathrm{red}_A$ from $J_H(M) = \mathrm{Pic}^0$ of the base change $\overline{\mathbb{Q}}\cdot F$ over $\overline{\mathbb{Q}}$ to $\mathrm{Pic}^0$ of $\bar F$ over $k_A$ (degree-zero divisors modulo principal ones in each case) maps the set $\{z : \ell^k z = 0\}$ onto the set $\{y : \ell^k y = 0\}$; that is, every $\ell^k$-torsion class of the special fibre is the reduction of an $\ell^k$-torsion class of $J_H(M)$.
--
--   This is the surjectivity half, in the residue characteristic, of the classical statement that reduction at a place of good reduction is an isomorphism on $\ell$-power torsion — the Deuring–Igusa good reduction of $X_H(M)$ for $\ell \nmid M$, together with the theory of the Néron model of its Jacobian. It is used, alongside injectivity of reduction on prime-to-$\ell$ torsion, in the computation of torsion cardinalities and of the reduction kernel inside the Tate module of $J_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_surjOn_reductionQExpModL_gammaH_torsion_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.surjOn_reductionQExpModL_gammaH_torsion_pow (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (h : ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H)) (k : ℕ) :
    Set.SurjOn (ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H))
      {z : ModularCurve.JH M H | (ℓ ^ k) • z = 0}
      {y : ModularCurve.JHC M H (IsLocalRing.ResidueField A) | (ℓ ^ k) • y = 0} := by sorry
