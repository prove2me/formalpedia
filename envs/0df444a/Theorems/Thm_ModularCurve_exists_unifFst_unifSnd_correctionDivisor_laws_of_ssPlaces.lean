-- Prove2me | Theorems.Thm_ModularCurve_exists_unifFst_unifSnd_correctionDivisor_laws_of_ssPlaces
-- name    : ModularCurve.exists_unifFst_unifSnd_correctionDivisor_laws_of_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/722dca32-0910-5ed0-940d-d8d49b19763c
-- title:
--   Uniformisers with correction divisors at supersingular places and their Frobenius translates
-- statement:
--   Let $q$ be a prime and $k$ an algebraically closed field of characteristic $q$, let $N\ge 1$ with $q\nmid N$, and let $F=$ `modularFunctionFieldC k N` be the subfield of the Laurent series field $k((T))$ generated over $k$ by the series `jqModC k` and `jqNModC k N`. Places of $F$ over $k$ are valuation subrings containing $k$, proper, and principal ideal rings; for a place $v$ and $f\in F$, $v.\mathrm{ord}(f)$ is minus the logarithm of the associated adic valuation, and the degree of a divisor is the $\mathbb{Z}$-linear extension of $v\mapsto v.\mathrm{deg}$. Let $W$ be a finite set of places all lying in `ssPlaces q N k`, i.e. each is rational, is an affine geometric place, and has $j$-value in `ssJSet q k`; let $U$ be a finite set of places disjoint from $W$ with $\mathrm{arithFrob}\cdot w\notin U$ for all $w\in W$, where $\mathrm{arithFrob}=$ `arithFrobC q k N` is the semilinear automorphism acting by the Frobenius on Laurent coefficients, and with $\#U\ge 2\,\mathrm{genusFF}(k,F)+2$, the genus being $\dim_k H^1(0)$. Then there exist maps $\pi^{(1)},\pi^{(2)}$ from places to $F$ and $R^{(1)},R^{(2)}$ from places to divisors such that for every $w\in W$: pointwise at every place $v$ one has $((w)+R^{(1)}_w)(v)=v.\mathrm{ord}(\pi^{(1)}_w)$, the divisor $R^{(1)}_w$ vanishes at every place of $W$, and $\deg R^{(1)}_w=-1$; and likewise $((\mathrm{arithFrob}\cdot w)+R^{(2)}_w)(v)=v.\mathrm{ord}(\pi^{(2)}_w)$, with $R^{(2)}_w$ vanishing on $W$ and of degree $-1$. The values of the four maps outside $W$ are unconstrained.
--
--   This provides, at each supersingular place of the level-$N$ fibre and at its arithmetic Frobenius translate, a global function which is a uniformiser there and has no zero or pole at any other place of the chosen finite set $W$, together with the correction divisor recording its remaining zeros and poles. It replaces, in positive genus, the level-one situation where $\tilde j-a_w$ has divisor $(w)-(\bar\infty)$ exactly; it is used in the construction of the annulus specialisation data of a prolongation tuple ([`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulusDatumLevel_laws`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulusDatumLevel_laws)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_unifFst_unifSnd_correctionDivisor_laws_of_ssPlaces.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.exists_unifFst_unifSnd_correctionDivisor_laws_of_ssPlaces
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (N : ℕ) [NeZero N]
    (hqN : ¬ q ∣ N)
    (W : Finset (Place k ↥(modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (U : Finset (Place k ↥(modularFunctionFieldC k N))) (hUW : Disjoint U W)
    (hUφ : ∀ w ∈ W, arithFrobC q k N • w ∉ U)
    (hU : 2 * genusFF k ↥(modularFunctionFieldC k N) + 2 ≤ U.card) :
    ∃ (unifFst unifSnd : Place k ↥(modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N))
      (corrFst corrSnd : Place k ↥(modularFunctionFieldC k N) → Divisor k ↥(modularFunctionFieldC k N)),
      ∀ w ∈ W,
        ((∀ v, (Finsupp.single w (1 : ℤ) + corrFst w) v = v.ord (unifFst w)) ∧ (∀ v ∈ W, corrFst w v = 0) ∧
          Divisor.degree (corrFst w) = -1) ∧
        ((∀ v, (Finsupp.single (arithFrobC q k N • w) (1 : ℤ) + corrSnd w) v = v.ord (unifSnd w)) ∧
          (∀ v ∈ W, corrSnd w v = 0) ∧ Divisor.degree (corrSnd w) = -1) := by sorry
