-- Prove2me | Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le
-- name    : ModularCurve.genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/ac743cd7-e533-5e15-b7b8-e8a65a14de3e
-- title:
--   Genus of the level-N modular function field in characteristic ℓ≥ 5
-- statement:
--   Let $K$ be an algebraically closed field, let $N$ be a nonzero natural number whose image $(N:K)$ in $K$ is nonzero, and let $\ell$ be a prime with $5 \le \ell$ such that $K$ has characteristic $\ell$. Inside $K((q))$ (Laurent series over $K$) let `modularFunctionFieldFullC K N` be the intermediate field obtained by adjoining to $K$ the set `divisorExpansionsC K N`, namely all series of the form `qExpand K d (jqModC K)` for nonzero divisors $d$ of $N$ — the $q$-substituted copies, indexed by $d \mid N$, of the $j$-expansion over $K$. Inside $\overline{\mathbb{Q}}((q))$ let `modularFunctionFieldBar N` be the base change `laurentBaseChange`, that is the field obtained by adjoining to $\overline{\mathbb{Q}}$ the coefficientwise image under `coeffEmb` of `modularFunctionFieldFull N`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by `divisorExpansions N`. The assertion is the equality of the two genera in the repartition sense, $\operatorname{genusFF}$, defined as the $K$-dimension of $H^1$ of the zero divisor: the genus of `modularFunctionFieldFullC K N` over $K$ equals the genus of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$.
--
--   This is Igusa's good-reduction statement for $X_0(N)$, restricted to residue characteristics $\ell \ge 5$ prime to $N$: the characteristic-$\ell$ modular function field of level $N$ has the same genus as the function field of $X_0(N)$ over $\overline{\mathbb{Q}}$, so no genus drop occurs. It feeds the unconditional genus computation for `modularFunctionFieldFullC` and thence the genus formula for $X_0(N)$ in characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
open AlgebraicCurve

theorem ModularCurve.genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hℓ : 5 ≤ ℓ) :
    genusFF K (modularFunctionFieldFullC K N) =
      genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by sorry
