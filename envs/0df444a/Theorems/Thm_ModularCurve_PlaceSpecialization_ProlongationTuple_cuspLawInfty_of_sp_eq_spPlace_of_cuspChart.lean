-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawInfty_of_sp_eq_spPlace_of_cuspChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/7ee0771c-6ef8-5f62-a4c1-85cab816588e
-- title:
--   Cusp law on the infinity branch for prolongation tuples
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$, $N$ a nonzero level, $k$ an algebraically closed field of characteristic $q$ and $\mathrm{red} : A \to k$ a ring homomorphism. Fix `data`, consisting of a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ vanishing on the pair $(j, j_q)$, together with the Kronecker congruence `hKr` asserting that the reduction of $\Phi$ modulo $q$ is $(C(X)^q - X)(C(X) - X^q)$, and integrality hypotheses $h\alpha$, $h\beta$ for the two Hecke maps `heckeAlphaBar`, `heckeBetaBar` at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$. Assume $q \nmid N$, let `fm` be a fibre model of level $N$ at $q$ over $A \to k$, let `hcc` be a cusp chart on it (i.e. $\bar{j}_N \cdot \bar{j}^{-N}$ lies in the infinity-side subring $\mathrm{BInf}$ and $\pi_{\mathrm{Inf}}$ sends it to $j_{q,N} \cdot j_q^{-N}$ in characteristic $q$), let $\mathrm{red}$ be surjective, let `dataAll` give modular polynomial data for every divisor of $N$, and let `hsep` assert that the level-$N$ polynomial, mapped to $k$ and then into $\mathrm{RatFunc}\ k$, is separable. Let $P$ be a place specialization for these data whose map `P.sp` on places equals the map `fm.spPlace hred dataAll hsep` attached to the model, and let $R$ be a prolongation tuple over $P$. Then $R$ satisfies `CuspLawInfty`: for every $f$ in the level-$Nq$ function field $\overline{\mathbb{Q}}$-base-changed, integral for both regular prolongations $R_1$, $R_2$ of $R$ with both residues nonzero, every divisor $D$ with $D(W) = \mathrm{ord}_W(f)$ at every place $W$, and every place $c$ satisfying `IsInftySide P`, the value at $P.\mathrm{reduceFst}(c)$ of the pushforward along $P.\mathrm{reduceFst}$ of the restriction of $D$ to the infinity-side places equals the order of the $R_1$-residue of $f$ at $P.\mathrm{reduceFst}(c)$.
--
--   This is the cusp law on the infinity component of the reduction of $X_0(Nq)$ at $q$ for $q \nmid N$, in the shape used here: the divisor of the reduced function on that component agrees, at the cusps, with the image of the infinity-side part of the divisor of $f$. It is used in the construction of charts at non-affine geometric places and in the production of a prolongation tuple that is a model and satisfies the fixed order law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawInfty_of_sp_eq_spPlace_of_cuspChart
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [IsAlgClosed k] (hqN : ¬ q ∣ N) (fm : CharPModel.FibreModel N A q k red)
    (hcc : fm.CuspChart)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hP : P.sp = fm.spPlace hred dataAll hsep)
    (R : ProlongationTuple P) : R.CuspLawInfty := by sorry
