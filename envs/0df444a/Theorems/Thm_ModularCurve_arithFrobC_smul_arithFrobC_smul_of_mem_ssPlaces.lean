-- Prove2me | Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces
-- name    : ModularCurve.arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/b3fb9c27-4813-5d8c-bfdb-3ae575d3ec09
-- title:
--   Frobenius squared fixes supersingular places of F_N
-- statement:
--   Let $q$ be a prime and $N \ge 1$, and let $K$ be an algebraically closed field of characteristic $q$. Write $F_N =$ `modularFunctionFieldC K N` for the intermediate field of the Laurent series field $K(\!(X)\!)$ obtained by adjoining to $K$ the two elements `jqModC K` and `jqNModC K N`. A place of $F_N/K$ is a valuation subring of $F_N$ containing the image of $K$, different from $F_N$ itself, and a principal ideal ring; the group $\mathrm{SemilinearAut}_K(F_N)$ of pairs $(\sigma,\tau) \in \mathrm{Aut}(F_N) \times \mathrm{Aut}(K)$ with $\sigma \circ \iota = \iota \circ \tau$ (for $\iota$ the structure map $K \to F_N$) acts on places. The element `arithFrobC q K N` is the semilinear automorphism `coeffSemilinearAut N (frobeniusEquiv K q)`, that is the pair consisting of the coefficientwise $q$-power map on $F_N$ and the $q$-power automorphism of $K$. The assertion is that for every place $w$ of $F_N/K$ lying in `ssPlaces q N K` — that is, $w$ is rational, satisfies `IsAffineGeomPlace K N`, and has `w.evalAt (jGeomGen K N)` in `ssJSet q K` — one has $\sigma \cdot (\sigma \cdot w) = w$ for $\sigma =$ `arithFrobC q K N`. Unlike the lemma [`ModularCurve.arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces_of_not_dvd`](thm.html#ModularCurve.arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces_of_not_dvd) it cites, no hypothesis $q \nmid N$ is imposed: the statement covers all levels.
--
--   This is the function-field form of Deuring's observation that the supersingular points of the modular curve of level $N$ in characteristic $q$ are defined over $\mathbb{F}_{q^2}$, the $q$-Frobenius of a supersingular curve having square a scalar and hence preserving all level structures. It feeds the Čerednik–Drinfeld-style constructions comparing supersingular places, Hecke transport and degeneracy maps under the arithmetic Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces
    (q N : ℕ) [NeZero N] (K : Type) [Field K] [DecidableEq K] [Fact q.Prime] [CharP K q]
    [IsAlgClosed K] :
    ∀ w ∈ ModularCurve.ssPlaces q N K,
      ModularCurve.arithFrobC q K N • (ModularCurve.arithFrobC q K N • w) = w := by sorry
