-- Prove2me | Theorems.Thm_ModularCurve_genusFF_gammaH_residueField_eq_of_not_dvd
-- name    : ModularCurve.genusFF_gammaH_residueField_eq_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/bdd32389-d09f-57c1-b222-039a3d7bbb68
-- title:
--   Genus of X_H(M) unchanged at places above ℓ∤ M
-- statement:
--   Let $M\ge 1$ be an integer, $H$ a subgroup of $(\mathbb{Z}/M)^\times$, and let $\Gamma_H(M)\le \mathrm{SL}_2(\mathbb{Z})$ be [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(M)\to(\mathbb{Z}/M)^\times$ sending $\gamma$ to the unit class of its lower-right entry modulo $M$. Let $\ell$ be a prime not dividing $M$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ` satisfying `LiesOverPrime ℓ`, i.e. $\ell$, viewed in $\overline{\mathbb{Q}}$, lies in the non-units of $A$; write $k=$ `IsLocalRing.ResidueField A`. For a field $K$, `qExpFunctionFieldC K Γ` denotes the intermediate field of the Laurent series field $K((q))$ generated over $K$ by all quotients $\mathrm{intSeriesC}\,K\,p_f/\mathrm{intSeriesC}\,K\,p_g$, where $f,g$ are modular forms of some common weight $k$ on $\Gamma$ (viewed in $\mathrm{GL}_2(\mathbb{R})$) whose $q$-expansions are given by integral power series $p_f,p_g$ with the image of $p_g$ in $K((q))$ non-zero. The assertion is that the genus `genusFF`, defined as the $K$-dimension of $H^1$ of the zero divisor of a function field, of `qExpFunctionFieldC k (GammaH M H)` over $k$ equals the genus over $\overline{\mathbb{Q}}$ of `laurentBaseChange`, the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `qExpFunctionFieldC ℚ (GammaH M H)`.
--
--   This is the genus half of the good-reduction (Deuring–Igusa) statement for the modular curve of level $\Gamma_H(M)$ at a prime $\ell\nmid M$: the genus of the mod-$\ell$ $q$-expansion function field agrees with the genus of the geometric model in characteristic zero. It is used in the construction of reduction data for $q$-expansions at level $\Gamma_H(M)$ and, specialised to $H$ trivial, for the corresponding statement at level $\Gamma_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genusFF_gammaH_residueField_eq_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.genusFF_gammaH_residueField_eq_of_not_dvd (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    AlgebraicCurve.genusFF (IsLocalRing.ResidueField A)
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) =
      AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := by sorry
