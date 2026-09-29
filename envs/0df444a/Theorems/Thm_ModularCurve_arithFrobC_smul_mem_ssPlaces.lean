-- Prove2me | Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces
-- name    : ModularCurve.arithFrobC_smul_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/d12e78c9-3f1e-5283-9f1d-56917f3387d2
-- title:
--   Arithmetic Frobenius preserves supersingular places
-- statement:
--   Let $q$ be a prime, let $N \ge 1$, and let $K$ be a perfect field of characteristic $q$. Write $F =$ `modularFunctionFieldC K N` for the intermediate field of the Laurent series field $K((t))$ generated over $K$ by the two elements `jqModC K` and `jqNModC K N`, and let `arithFrobC q K N` be the semilinear automorphism of $F$ over $K$ given by the pair consisting of the coefficientwise $q$-power map `coeffRingAut N (frobeniusEquiv K q)` on $F$ and the $q$-power Frobenius `frobeniusEquiv K q` on $K$; these pairs form the group `SemilinearAut K F` of pairs of ring automorphisms of $F$ and of $K$ compatible with the structure map $K \to F$, and this group acts on places. The assertion is that for every place $w$ of $F$ over $K$, i.e. every valuation subring of $F$ containing the image of $K$, distinct from $F$ and a principal ideal ring, which lies in [`ModularCurve.ssPlaces q N K`](def/ModularCurve_SupersingularNodePlaces.html#L113) — that is, $w$ is rational, satisfies `IsAffineGeomPlace K N w`, and has $w$-value `w.evalAt (jGeomGen K N)` of the first geometric generator lying in the set `ssJSet q K` — the translated place `arithFrobC q K N • w` again lies in [`ModularCurve.ssPlaces q N K`](def/ModularCurve_SupersingularNodePlaces.html#L113).
--
--   This records that the supersingular locus in the set of places of the level-$N$ modular function field in characteristic $q$ is stable under the arithmetic Frobenius, the geometric counterpart being that Frobenius permutes the supersingular points of the special fibre. It is used in the Čerednik–Drinfeld stage of the argument, in particular in the statements about joint constructions of semistable specialisations and Hecke transport along degeneracy maps, and in the study of the $j$-shadow of level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.arithFrobC_smul_mem_ssPlaces (q N : ℕ) [NeZero N] (K : Type) [Field K]
    [DecidableEq K] [Fact q.Prime] [CharP K q] [PerfectField K] :
    ∀ w ∈ ModularCurve.ssPlaces q N K,
      ModularCurve.arithFrobC q K N • w ∈ ModularCurve.ssPlaces q N K := by sorry
