-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawZero_oneSided_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawZero_oneSided_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/06531317-a08b-5e44-a7f7-eb97549b2e99
-- title:
--   One-sided cusp law at zero, auxiliary level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$, together with modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$), a proof `hKr` of the Kronecker congruence that the reduction of $\Phi$ modulo $q$ equals $(X^q - Y)(X - Y^q)$ in the bivariate convention used, and proofs $h\alpha$, $h\beta$ that the two Hecke maps $\overline{\alpha}$, $\overline{\beta}$ at auxiliary level $1$ and prime $q$ are integral ring homomorphisms. Let $P$ be a place specialisation of these data at auxiliary level $N = 1$ and let $R$ be a prolongation tuple over $P$ satisfying `R.IsModel`, i.e. the conjunction of the two divisor laws and the cusp laws at $\infty$ and at $0$. The conclusion is: for every $f$ in the modular function field $\overline{F}(1 \cdot q)$ that lies in the integers of the second regular prolongation $R.R_2$ and whose residue $R.R_2$-residue is non-zero, for every divisor $D$ on the places of $\overline{F}(1 \cdot q)$ over $\overline{\mathbb{Q}}$ with $D(W) = \operatorname{ord}_W f$ for all $W$, and for every place $c$ on the zero side for $P$ (that is, $c$ is `IsCuspidal'` for $P$ and there is $\tau \in A$ with $\mathrm{red}\,\tau = 1$ such that $c$ has value $\tau$ at $t_0$), the pushforward along $P.\mathrm{reduceSnd}$ of $D$ restricted to the zero-side places, evaluated at $P.\mathrm{reduceSnd}\,c$, equals the order of $R.\mathrm{residue}_2\langle f\rangle$ at $P.\mathrm{reduceSnd}\,c$. Here $P.\mathrm{reduceSnd}\,W$ is obtained by restricting $W$ along $\overline{\beta}$ and applying the specialisation map $P.\mathrm{sp}$.
--
--   This is the zero-side counterpart of the cusp law at $\infty$, specialised to auxiliary level $N = 1$ (so that the coprimality condition $q \nmid N$ is automatic), and it is stated at an arbitrary zero-side place rather than only at the cusp $0$: the degree of the part of the divisor of $f$ concentrated on the zero side above a given reduced place is computed by the order of the residue of $f$ there. It feeds the construction of good divisors and of the annulus and component charts attached to a model prolongation tuple.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawZero_oneSided_levelOne.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve

open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawZero_oneSided_levelOne {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel) :
    ∀ (f : modularFunctionFieldBar (1 * q)) (h₂ : f ∈ R.R₂.integers),
      R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
        (∀ W, D W = W.ord f) →
        ∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
          IsZeroSide P c →
          Finsupp.mapDomain P.reduceSnd (D.filter (IsZeroSide P)) (P.reduceSnd c)
            = (P.reduceSnd c).ord (R.residue₂ ⟨f, h₂⟩) := by sorry
