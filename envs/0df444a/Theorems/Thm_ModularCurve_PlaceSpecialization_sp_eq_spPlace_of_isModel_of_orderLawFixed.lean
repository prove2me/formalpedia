-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_sp_eq_spPlace_of_isModel_of_orderLawFixed
-- name    : ModularCurve.PlaceSpecialization.sp_eq_spPlace_of_isModel_of_orderLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/4dda9283-a2da-5ecc-b503-f3c7bf0590a0
-- title:
--   Model and order laws pin the place specialisation of X₀(N)
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $\kappa=\mathrm{ResidueField}(A)$ has characteristic $q$, and $N$ a nonzero level with $q \nmid N$. Fix `data`, a `ModularPolynomialData q`, i.e. a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions, together with `hKr`, the Kronecker congruence asserting that the bivariate reduction of $\Phi$ modulo $q$ equals $(C X^q - X)(C X - X^q)$, and `hα`, `hβ`, the integrality of the two Hecke maps $\bar\alpha$, $\bar\beta$ at level $N$ and prime $q$. Let $P$ be any place specialisation of level $N$ at $A$ with target field $\kappa$ and reduction the canonical residue map, and let $R$ be a prolongation tuple over $P$ satisfying `IsModel` (the two divisor laws and the cusp laws at $\infty$ and at $0$) and `OrderLawFixed`: for every $f$ in the function field at level $Nq$ lying in the integer rings of both regular prolongations $R_1$, $R_2$ with nonzero residues, every divisor $D$ whose coefficient at each place $W$ is $W(f)$, and every affine geometric place $v$ of $\mathrm{modularFunctionFieldC}\ \kappa\ N$ fixed by the square of the geometric Frobenius on places, the pushforward of $D$ along $P.\mathrm{reduceFst}$ takes at $v$ the value $\mathrm{ord}_v(R.\mathrm{residue}_1 f) + \mathrm{ord}_{\varphi v}(R.\mathrm{residue}_2 f)$. Let further `fm` be a fibre model of level $N$ over $A$ at $q$ with values in $\kappa$ and canonical reduction, `hc` a cusp chart for it (so $\bar{j_N}\,\bar{j}^{-N}$ lies in the subring at $\infty$ and reduces to $j_{q,N}\,j_q^{-N}$), `hred` surjectivity of the residue map $A \to \kappa$, `dataAll` a choice of modular polynomial data for every divisor $d$ of $N$, and `hsep` the separability of the image of $\Phi_N$ in $\mathrm{RatFunc}(\kappa)$. Then $P.\mathrm{sp} = \mathrm{fm}.\mathrm{spPlace}$, an equality of maps from places of the base-changed modular function field of level $N$ over $\overline{\mathbb{Q}}$ to places of $\mathrm{modularFunctionFieldC}\ \kappa\ N$, at all places, cusps included.
--
--   This is the uniqueness half of the reduction of $X_0(N)$ modulo a prime $q$ not dividing $N$: the divisor and cusp laws together with the order law at the Frobenius-fixed affine places determine the specialisation map on places completely, identifying any abstract place specialisation with the one attached to a fibre model. It is used by the level-model rows of the Deligne–Rapoport model package, for instance to identify the place of a point with its reduction and to produce common units with prescribed poles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_sp_eq_spPlace_of_isModel_of_orderLawFixed.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.sp_eq_spPlace_of_isModel_of_orderLawFixed
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    [CharP (IsLocalRing.ResidueField ↥A) q]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ}
    (R : ProlongationTuple P) (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (fm : CharPModel.FibreModel N A q (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A)) (hc : fm.CuspChart)
    (hred : Function.Surjective (IsLocalRing.residue ↥A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField ↥A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField ↥A)) (RatFunc (IsLocalRing.ResidueField ↥A)))).Separable) :
    P.sp = fm.spPlace hred dataAll hsep := by sorry
