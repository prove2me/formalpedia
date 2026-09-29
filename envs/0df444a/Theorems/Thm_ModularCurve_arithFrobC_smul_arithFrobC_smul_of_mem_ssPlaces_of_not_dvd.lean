-- Prove2me | Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces_of_not_dvd
-- name    : ModularCurve.arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/6e8b88f3-0720-58bd-a534-530a644f0ceb
-- title:
--   Squared arithmetic Frobenius fixes supersingular places, q ∤ N
-- statement:
--   Let $q$ and $N$ be natural numbers with $N \neq 0$ and $q \nmid N$, let $q$ be prime, and let $K$ be an algebraically closed field of characteristic $q$. Write $F_N$ for `modularFunctionFieldC K N`, the intermediate field of the Laurent series field $K((t))$ generated over $K$ by `jqModC K` and `jqNModC K N`, and let `arithFrobC q K N` be the semilinear automorphism of $F_N$ over $K$ given by the pair consisting of the coefficientwise $q$-th power map `coeffRingAut N (frobeniusEquiv K q)` on $F_N$ and the $q$-power Frobenius `frobeniusEquiv K q` on $K$ (a pair compatible with the structure map $K \to F_N$). Such semilinear automorphisms act on the set of places of $F_N$ over $K$, a place being a valuation subring of $F_N$ containing the image of $K$, different from $F_N$ itself, and a principal ideal ring. The assertion is that for every place $w$ of $F_N$ over $K$ lying in `ssPlaces q N K`, that is, every $w$ which is rational, satisfies `IsAffineGeomPlace K N w`, and whose value `w.evalAt (jGeomGen K N)` lies in the set `ssJSet q K` of supersingular $j$-invariants, one has $\sigma \cdot (\sigma \cdot w) = w$ for $\sigma$ equal to `arithFrobC q K N`.
--
--   This is the statement that the supersingular points of the modular curve of level $N$ in characteristic $q$, with $q \nmid N$, are fixed by the square of the arithmetic Frobenius, i.e. are rational over $\mathbb{F}_{q^2}$ in the relevant sense; classically it goes back to Deuring's theory of supersingular elliptic curves. It is used in the analysis of prolongations of place specialisations at supersingular places, where the fixed-point property of $\sigma^2$ supplies the common units and poles required by the regularity laws.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces_of_not_dvd.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces_of_not_dvd
    (q N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (K : Type) [Field K] [DecidableEq K] [Fact q.Prime]
    [CharP K q] [IsAlgClosed K] :
    ∀ w ∈ ModularCurve.ssPlaces q N K,
      ModularCurve.arithFrobC q K N • (ModularCurve.arithFrobC q K N • w) = w := by sorry
