-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/c75f3bfe-66f6-5094-a1c8-4b2ea627b55a
-- title:
--   Subtracting a balanced strict divisor preserves twist data
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$, together with modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, and witnesses `hα`, `hβ` that the two degeneracy maps $\overline{F}_N \to \overline{F}_{Nq}$ between the base-changed modular function fields are integral. Let $P$ be a place specialisation with these data, $R$ a prolongation tuple over $P$, $W$ a finite set of places of `modularFunctionFieldC k N`, and `dat` an annulus datum for $R$ over $W$ (node coordinates, widths, depths, uniformisers, correction divisors and units $u_0$, $\lambda$, $\mu$ at each place of $W$). Let $X$ and $D_t$ be divisors on `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$, i.e. finitely supported $\mathbb{Z}$-valued functions on places, and assume that every place in the support of $D_t$ satisfies `P.IsStrictFst` or `P.IsStrictSnd`, and that the two strict parts `P.fstDiv Dt` and `P.sndDiv Dt` — the restrictions of $D_t$ to the places with the respective strictness property — both have degree $0$. Let $a = (a_Z, a_{Z'}, a_E)$ be a twist vector over $W$ and assume `dat.IsTwistOf a X`, that is: the degree of `P.fstDiv X` is minus the sum over $w \in W$ of the first end orders of $(a, X)$ at $w$, the degree of `P.sndDiv X` is minus the corresponding sum of second end orders, and for every $w \in W$ and every $d$ with $1 \le d$ and $d + 1 \le \mathrm{width}(w)$ the circle degree of $X$ at $(w, d)$ equals minus the second difference of the chain values of $a$ at $d$. The conclusion is twofold: $a$ is again a twist vector of $X - D_t$ in this sense, and the specialisation datum of $(a, X - D_t)$ equals that of $(a, X)$ minus `P.glueData` of $D_t$ on the set of node pairs $(w, \mathrm{Frob}\cdot w)$ for $w \in W$, where the latter is the triple consisting of the pushforward of `P.fstDiv Dt` along `P.reduceFst`, the pushforward of `P.sndDiv Dt` along `P.reduceSnd`, and the trivial family of node units.
--
--   This is the bookkeeping step showing that divisors supported on strict places are invisible to all annulus-read quantities of an annulus datum at level $N$ (circle degrees, end orders, angular factors and node units), so that subtracting such a balanced divisor changes the specialisation datum only by its plain, untwisted gluing contribution. It is used in the assembly of kernel elements for the specialisation of the Jacobian, in `exists_fixedStrict_add_kernelGood_of_isTwistOf_of_inertiaStable`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict.lean

import Mathlib
import Definitions.Def_ModularCurve_AnnulusSpecializationLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (dat : R.AnnulusDatumLevel W)
    (X Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    (hdeg₁ : Divisor.degree (P.fstDiv Dt) = 0) (hdeg₂ : Divisor.degree (P.sndDiv Dt) = 0)
    (a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W)
    (ha : dat.IsTwistOf a X) :
    dat.IsTwistOf a (X - Dt) ∧
      dat.spData a (X - Dt) = dat.spData a X - P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) Dt := by sorry
