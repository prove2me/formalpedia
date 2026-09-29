-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_eq_zero_of_mem_integersSnd_of_coe_eq_modularUnitSeries
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.residue_eq_zero_of_mem_integersSnd_of_coe_eq_modularUnitSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/3fb40ead-459e-51d9-ab7c-85ec4090b18d
-- title:
--   Second residue of the level-q modular unit vanishes
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N \ge 1$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$, together with a datum `data` consisting of a monic polynomial $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, the hypothesis `hKr` that the bivariate reduction of $\Phi$ modulo $q$ equals $(X^q - Y)(X - Y^q)$ in the library's normalisation, and the hypotheses `hα`, `hβ` that the two degeneracy inclusions `heckeAlphaBar`, `heckeBetaBar` of the base-changed level-$N$ modular function field into level $Nq$ are integral. Assume $q \nmid N$, let $P$ be a place specialization datum of type `PlaceSpecialization A q N data hKr k red hα hβ`, and let $R$ be a prolongation tuple over $P$; in particular $R$ supplies two regular prolongations $R_1, R_2$ of $A$ to the field `modularFunctionFieldBar (N * q)` with residue field the full level-$N$ modular function field over the residue field of $A$, where membership in $R_2$'s valuation subring and the residue map of $R_2$ are those of $R_1$ composed with the Atkin–Lehner transport `atkinLehnerBar N q`. Let $u$ be an element of `modularFunctionFieldBar (N * q)` whose underlying Laurent series is the image under `coeffEmb` of `modularUnitSeries q` $= \Delta/\Delta_q$, and suppose $u$ lies in $R_1$'s valuation subring with nonzero $R_1$-residue. Then for every proof that $u$ lies in $R_2$'s valuation subring, its $R_2$-residue is $0$.
--
--   The underlying classical input is the relation $u \cdot w_q(u) = q^{12}$ for the modular unit $u = \Delta/\Delta_q$ under the Fricke involution at $q$, so that in characteristic $q$ the unit cannot have nonzero residue on both sides of the Kronecker reduction. It is used in the analysis of residue orders and of the cusp laws for the two prolongations at composite level $Nq$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_eq_zero_of_mem_integersSnd_of_coe_eq_modularUnitSeries.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open ModularCurve AlgebraicCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.residue_eq_zero_of_mem_integersSnd_of_coe_eq_modularUnitSeries
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (h₁ : u ∈ R.R₁.integers) (hres₁ : R.R₁.residue ⟨u, h₁⟩ ≠ 0) :
    ∀ h₂ : u ∈ R.R₂.integers, R.R₂.residue ⟨u, h₂⟩ = 0 := by sorry
