-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_moments_from_good
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.moments_from_good
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:23:49.795893+00:00
-- url     : https://prove2.me/theorems/78f28ec0-11ef-43d2-a133-1f4f8da02cd5
-- title:
--   Variance bound from exact first and second moments outside a small bad set
-- statement:
--   For a nonempty finite set $X$ and $h:X\to\mathbb R$ write $\operatorname{avg}_{x\in X}h(x)=\frac1{|X|}\sum_{x\in X}h(x)$ for the uniform average.
--
--   Let $\Omega$ and $Y$ be nonempty finite sets and let $f:Y\times\Omega\to\mathbb R$ take values in $[0,1]$. Let $G\subseteq Y$ be a set of good indices and $G_2\subseteq Y\times Y$ a set of good ordered pairs, and let $p,a$ be real numbers with $0\le p\le 1$. Assume
--
--   1. $\operatorname{avg}_{\omega\in\Omega} f(y,\omega)=p$ for every $y\in G$;
--   2. $\operatorname{avg}_{\omega\in\Omega} f(y,\omega)\,f(y',\omega)=p^2$ for every $(y,y')\in G_2$;
--   3. the proportion of bad indices is small: $|Y\setminus G|/|Y|\le a$;
--   4. the proportion of bad pairs is small: $|(Y\times Y)\setminus G_2|/|Y|^2\le a$.
--
--   Then
--
--   $$
--   \operatorname{avg}_{\omega\in\Omega}\Big(\operatorname{avg}_{y\in Y}f(y,\omega)-p\Big)^2\le 3a .
--   $$
--
--   The first and second moments are only required to be exact on good indices and good pairs; bad indices and pairs are charged at worst-case cost, using only that $f$ takes values in $[0,1]$. Together with Chebyshev's inequality this shows that, for most $\omega$, the empirical density $\operatorname{avg}_{y}f(y,\omega)$ is close to $p$. It is the abstract second-moment step in the analysis of random slot configurations.
--
--   **Formalization Note** The proportions of bad indices and bad pairs are written as averages of the indicator functions `if good y then 0 else 1` over $Y$ and over $Y\times Y$, with `good`, `good₂` decidable predicates. Only unconditional averages appear; no conditional probabilities are used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Averages.lean#L156-L180

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

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uΩ uI uΛ uK uA uJ uY
open scoped BigOperators
open Finset
variable {Ω : Type uΩ} [Fintype Ω] [Nonempty Ω]

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.moments_from_good {Y : Type uY} [Fintype Y] [Nonempty Y]
    (f : Y → Ω → ℝ) (good : Y → Prop) (good₂ : Y × Y → Prop)
    [DecidablePred good] [DecidablePred good₂] {p a : ℝ}
    (hp : 0≤p) (hp1 : p≤1) (hf : ∀ y ω, 0≤f y ω ∧ f y ω≤1)
    (hfirst : ∀ y, good y → avg (f y)=p)
    (hsecond : ∀ yy, good₂ yy → avg (fun ω ↦ f yy.1 ω*f yy.2 ω)=p^2)
    (hbad : avg (fun y ↦ if good y then 0 else 1)≤a)
    (hbad₂ : avg (fun yy ↦ if good₂ yy then 0 else 1)≤a) :
    avg (fun ω ↦ (avg (fun y ↦ f y ω)-p)^2) ≤ 3*a := by sorry
