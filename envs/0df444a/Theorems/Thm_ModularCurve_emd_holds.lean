-- Prove2me | Theorems.Thm_ModularCurve_emd_holds
-- name    : ModularCurve.emd_holds
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/bca9d32d-6e03-5019-b056-04ad0fdbcc7f
-- title:
--   EMD holds at every level N and every j₀
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $j_0$ be an element of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. The assertion is that the predicate `EMD N j₀` holds, that is: there is a Weierstrass curve $E_0$ over $\overline{\mathbb{Q}}$ which is elliptic and satisfies $j(E_0) = j_0$, together with a bijection $\Phi$ between the type `Emb N j₀` — whose elements have as first component an $\overline{\mathbb{Q}}$-algebra homomorphism from the level-$N$ field `modularFunctionFieldBar N` into the Hahn series ring `HahnSeries ℚ (AlgebraicClosure ℚ)` — and the type `CycSub E₀ N` of those additive subgroups $H$ of the group of affine points of $E_0$ for which $H = \langle g\rangle$ is the group of integer multiples of some point $g$ of additive order exactly $N$, such that for all $\psi, \psi'$ in `Emb N j₀` the following are equivalent: (i) `SamePlace`, i.e. there is a place $w$ of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ induced by the homomorphism underlying $\psi$ and also by the one underlying $\psi'$; and (ii) `SameOrbit` for the subgroups $\Phi(\psi)$ and $\Phi(\psi')$, i.e. there is a variable change $\gamma$ over $\overline{\mathbb{Q}}$ with $\gamma \bullet E_0 = E_0$ and generators $g$, $g'$ of the two subgroups with $g'$ equal to the image of $g$ under `Point.vcInvFun γ E₀.toAffine`.
--
--   This is the local comparison, at the level of places above $j_0$, between normalised embeddings of the level-$N$ modular function field into Hahn series and the cyclic subgroups of order $N$ of an elliptic curve with $j$-invariant $j_0$, the two sides being matched so that coincidence of the induced place corresponds to conjugacy of subgroups under automorphisms of the curve. It is used in the analysis of the Riemann–Roch spaces and in the genus computation for `modularFunctionFieldBar N`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_emd_holds.lean

import Definitions.Def_ModularCurve_EMD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.emd_holds (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ) :
    EMD N j₀ := by sorry
