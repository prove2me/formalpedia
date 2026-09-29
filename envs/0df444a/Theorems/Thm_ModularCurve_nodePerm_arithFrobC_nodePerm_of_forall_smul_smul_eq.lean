-- Prove2me | Theorems.Thm_ModularCurve_nodePerm_arithFrobC_nodePerm_of_forall_smul_smul_eq
-- name    : ModularCurve.nodePerm_arithFrobC_nodePerm_of_forall_smul_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/eaa1d57f-0346-5197-9b53-f2ba16ab80d0
-- title:
--   Frobenius node permutation is an involution
-- statement:
--   Let $q$ be a prime, $N$ a positive integer, and $k$ a perfect field of characteristic $q$. Write $F =$ `modularFunctionFieldC k N` for the intermediate field of the Laurent series field $k((X))$ generated over $k$ by `jqModC k` and `jqNModC k N`, and let $\varphi =$ `arithFrobC q k N` be the semilinear automorphism of $F$ over $k$ given by the pair consisting of the coefficientwise automorphism `coeffRingAut N` attached to the Frobenius $x \mapsto x^q$ of $k$ together with that Frobenius itself; here a semilinear automorphism is a pair in $\operatorname{RingAut} F \times \operatorname{RingAut} k$ compatible with the structure map, and a place of $F$ over $k$ is a valuation subring of $F$ containing $k$, distinct from $F$, and a principal ideal ring. Let $W$ be a finite set of such places, and put $S =$ `nodePairsOfPlaces` $\varphi\, W$, the image of $W$ under the injective map `smulNodePair` $\varphi$ into pairs of places. Assume (i) $\varphi \cdot (\varphi \cdot w) = w$ for every $w \in W$, and (ii) $S$ is node-stable for $\varphi$, i.e. $(\varphi \cdot s_1, \varphi \cdot s_2) \in S$ whenever $(s_1,s_2) \in S$. Then the resulting permutation `nodePerm` of $S$, which sends $(s_1,s_2)$ to $(\varphi \cdot s_1, \varphi \cdot s_2)$, satisfies that its square fixes every element of $S$; that is, it is an involution.
--
--   This is the level-$N$, place-theoretic form of the statement that the Frobenius-induced permutation of the nodes of the two-copy special fibre at $q$ is an involution, the hypothesis that $\varphi^2$ fixes $W$ being the counterpart of the fact that supersingular $j$-invariants lie in $\mathbb{F}_{q^2}$. It is a purely combinatorial ingredient in the analysis of the Hecke operator at $q$ on node units, and is used in [`ModularCurve.jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_and_smul_heckeGen_eq_of_isFrobeniusAt_of_ne`](thm.html#ModularCurve.jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_and_smul_heckeGen_eq_of_isFrobeniusAt_of_ne) and in [`ModularCurve.nonempty_jZeroSemistableSpecialization`](thm.html#ModularCurve.nonempty_jZeroSemistableSpecialization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_nodePerm_arithFrobC_nodePerm_of_forall_smul_smul_eq.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve ModularCurve

theorem ModularCurve.nodePerm_arithFrobC_nodePerm_of_forall_smul_smul_eq
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k]
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hfix : ∀ w ∈ W, arithFrobC q k N • (arithFrobC q k N • w) = w)
    (hstab : SemilinearAut.IsNodeStable (nodePairsOfPlaces (arithFrobC q k N) W)
      (arithFrobC q k N))
    (s : ↥(nodePairsOfPlaces (arithFrobC q k N) W)) :
    SemilinearAut.nodePerm (nodePairsOfPlaces (arithFrobC q k N) W) (arithFrobC q k N) hstab
        (SemilinearAut.nodePerm (nodePairsOfPlaces (arithFrobC q k N) W) (arithFrobC q k N)
          hstab s) = s := by sorry
