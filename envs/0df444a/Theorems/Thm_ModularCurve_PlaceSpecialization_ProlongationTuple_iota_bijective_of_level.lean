-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_iota_bijective_of_level
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.iota_bijective_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/2683a489-e99d-50e1-8ed5-0b402e270eed
-- title:
--   Bijectivity of ι for a level-N prolongation tuple
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an integer $N\ge 1$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$. Let `data` be modular polynomial data at level $q$, i.e. a monic $\Phi\in\mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j,\,j(q\,\cdot))$ of $q$-expansions, let `hKr` assert the Kronecker congruence that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q-X)(C(X)-X^q)$, and let $h\alpha$, $h\beta$ assert that the two Hecke maps `heckeAlphaBar` and `heckeBetaBar` from the Laurent base change over $\overline{\mathbb{Q}}$ of the full modular function field of level $N$ into that of level $Nq$ are integral ring homomorphisms. Let $P$ be a place specialisation of these data over $(k,\mathrm{red})$ and let $R$ be a prolongation tuple over $P$, so that in particular $R$ supplies a ring homomorphism $\overline{\mathrm{red}}\colon \kappa_A\to k$ on the residue field of $A$ with $\overline{\mathrm{red}}\circ\mathrm{res}_A=\mathrm{red}$, together with the comparison homomorphism $\iota$ from the full reduced modular function field of level $N$ over $\kappa_A$ to the reduced modular function field of level $N$ over $k$, acting coefficientwise by $\overline{\mathrm{red}}$ on Laurent $q$-expansions. Assume $q\nmid N$. Then $\iota$ is bijective.
--
--   The statement identifies the characteristic-$q$ function field attached to a prolongation tuple over the residue field of $A$ with the function field over $k$ used in the place specialisation, under the assumption that the level is prime to $q$. It is used in the construction of the model-theoretic data on $X_0(N)$ in characteristic $q$, in particular in [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq_of_isModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_iota_bijective_of_level.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization.ProlongationTuple
open ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.iota_bijective_of_level
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) (hqN : ¬ q ∣ N) :
    Function.Bijective R.ι := by sorry
