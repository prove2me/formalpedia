-- Prove2me | Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFullC_mul_dedekindPsi
-- name    : ModularCurve.relfinrank_modularFunctionFieldFullC_mul_dedekindPsi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/ff4d0c68-f55b-58cd-8853-24236665c233
-- title:
--   Both degeneracy inclusions multiply ψ by the same index
-- statement:
--   Let $K$ be a field and let $N,q$ be nonzero natural numbers such that the image of $Nq$ in $K$ is nonzero. For a nonzero natural number $M$, write $F_M$ for `modularFunctionFieldFullC K M`, the intermediate field of $K((q))$ (realised as `LaurentSeries K`) obtained by adjoining to $K$ the set of all $\mathrm{qExpand}\,K\,d\,(j)$ with $d$ a nonzero divisor of $M$, i.e. the substitutions $q \mapsto q^{d}$ applied to the $q$-expansion `jqModC K` of the modular invariant; and let $\psi(M) = \sum_{d \mid M,\ d \text{ squarefree}} M/d$ be `dedekindPsi M`. Let $\sigma =$ `qExpandAlgHomC K q` be the injective $K$-algebra endomorphism of $K((q))$ given on Hahn-series exponents by multiplication by $q$, that is the substitution $q \mapsto q^{q}$. The theorem asserts two equalities of natural numbers: first, the relative degree (`IntermediateField.relfinrank`) of $F_{Nq}$ over $F_N$, multiplied by $\psi(N)$, equals $\psi(Nq)$; second, the relative degree of $F_{Nq}$ over the image $\sigma(F_N)$, multiplied by $\psi(N)$, again equals $\psi(Nq)$.
--
--   This records that, on the level of the $q$-expansion function fields, both degeneracy coverings $X_0(Nq) \rightrightarrows X_0(N)$ — the inclusion $F_N \subseteq F_{Nq}$ and the one induced by $q \mapsto q^{q}$ — have degree $\psi(Nq)/\psi(N)$, over any field in which $Nq$ is invertible, so that the degrees agree in characteristic $0$ and in characteristic $\ell \nmid Nq$. It is used in the comparison of degeneracy maps and Hecke correspondences on $X_0(N)$ and their reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_relfinrank_modularFunctionFieldFullC_mul_dedekindPsi.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.relfinrank_modularFunctionFieldFullC_mul_dedekindPsi
    (K : Type*) [Field K] (N q : ℕ) [NeZero N] [NeZero q] (hNq : ((N * q : ℕ) : K) ≠ 0) :
    IntermediateField.relfinrank (modularFunctionFieldFullC K N) (modularFunctionFieldFullC K (N * q))
        * dedekindPsi N = dedekindPsi (N * q) ∧
    IntermediateField.relfinrank ((modularFunctionFieldFullC K N).map (qExpandAlgHomC K q))
        (modularFunctionFieldFullC K (N * q)) * dedekindPsi N = dedekindPsi (N * q) := by sorry
