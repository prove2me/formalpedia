-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_exists_few_bad_centers_averaged
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.exists_few_bad_centers_averaged
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:34:24.615445+00:00
-- url     : https://prove2.me/theorems/ad0f619d-f60c-4140-a2e5-9d6551d2cb23
-- title:
--   A sample point with few large deviations from an averaged second-moment bound
-- statement:
--   Let $\Omega$ be a finite nonempty set, $I$ a finite set and $K$ a finite nonempty set. For a function $F$ on a finite set $X$ write $\operatorname{avg}_{x\in X}F(x)=\frac{1}{|X|}\sum_{x\in X}F(x)$. Let $Z:I\times K\times\Omega\to\mathbb{R}$, $(i,s,\omega)\mapsto Z_i(s,\omega)$, be any function, let $p,a\in\mathbb{R}$ and let $t>0$. Suppose that for every $i\in I$
--   $$\operatorname{avg}_{\omega\in\Omega}\ \operatorname{avg}_{s\in K}\big(Z_i(s,\omega)-p\big)^2\le a .$$
--   Then there exists $\omega\in\Omega$ such that
--   $$\#\big\{(i,s)\in I\times K:\ |Z_i(s,\omega)-p|\ge t\big\}\ \le\ \frac{|I|\,|K|\,a}{t^2}.$$
--
--   This is a Chebyshev-type selection principle: a mean-square bound for a family of random variables indexed by $I\times K$, with $\omega$ uniformly distributed on $\Omega$, produces one realization in which only few indices deviate from $p$ by at least $t$. In the slot-hypergraph argument it selects a configuration for which only few slot vertices have an atypical slot density, so that these vertices can be pruned.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/DependentMoments.lean#L477-L495

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uκ uA uJ uY uV uK uΩ uI
open scoped BigOperators
open Finset

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.exists_few_bad_centers_averaged {Ω : Type uΩ} {I : Type uI} {K : Type uK} [Fintype Ω] [Nonempty Ω]
    [Fintype I] [Fintype K] [Nonempty K] (Z : I → K → Ω → ℝ)
    (p : ℝ) {t a : ℝ} (ht : 0<t)
    (hZ : ∀ i, avg (fun ω ↦ avg (fun s ↦ (Z i s ω-p)^2))≤a) :
    ∃ ω, ((Finset.univ.filter (fun v : I × K ↦ t≤|Z v.1 v.2 ω-p|)).card : ℝ) ≤
      Fintype.card I*Fintype.card K*a/t^2 := by sorry
