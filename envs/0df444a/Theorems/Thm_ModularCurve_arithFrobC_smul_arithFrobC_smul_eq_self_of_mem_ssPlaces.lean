-- Prove2me | Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces
-- name    : ModularCurve.arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/9b533bde-e0c0-5fb9-bf59-e89c543e1a28
-- title:
--   Arithmetic Frobenius squared fixes the supersingular places
-- statement:
--   Let $q$ be a prime and $N$ a nonzero natural number with $q \nmid N$, and let $K$ be an algebraically closed field of characteristic $q$. Write $F =$ `modularFunctionFieldC K N` for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the two series `jqModC K` and `jqNModC K N` (the $q$-expansion of $j$ and its $N$-fold expansion). Let $w$ be a place of $F$ over $K$ in the sense of the project, i.e. a valuation subring of $F$ containing $\mathrm{algebraMap}(K)$, not equal to all of $F$, and a principal ideal ring, and assume $w$ lies in `ssPlaces q N K`: $w$ is rational, satisfies `IsAffineGeomPlace K N`, and the value of $w$ at `jGeomGen K N` belongs to the set `ssJSet q K` of supersingular $j$-invariants in $K$. Let `arithFrobC q K N` be the coefficientwise arithmetic Frobenius, namely the element of the group of semilinear automorphisms (pairs $(\sigma,\tau) \in \mathrm{RingAut}\,F \times \mathrm{RingAut}\,K$ with $\sigma \circ \mathrm{algebraMap} = \mathrm{algebraMap} \circ \tau$) obtained from $\tau =$ `frobeniusEquiv K q` acting on coefficients. Then applying the induced pointwise action of this semilinear automorphism twice to $w$ returns $w$.
--
--   This is the statement that the supersingular points of the level-$N$ modular curve in characteristic $q$, with $q \nmid N$, are fixed by the square of the arithmetic Frobenius, the function-field form of Deuring's theorem that supersingular $j$-invariants and the associated cyclic $N$-subgroups are defined over $\mathbb{F}_{q^2}$. It feeds the analysis of the supersingular (crossing) points in the Deligne–Rapoport model at level $N$, and is cited by the results constructing node data and identifying closed points of that model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces
    (q N : ℕ) [Fact q.Prime] [NeZero N] (hqN : ¬ q ∣ N) (K : Type*) [Field K] [CharP K q] [IsAlgClosed K]
    [DecidableEq K] (w : AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldC K N))
    (hw : w ∈ ModularCurve.ssPlaces q N K) :
    ModularCurve.arithFrobC q K N • (ModularCurve.arithFrobC q K N • w) = w := by sorry
