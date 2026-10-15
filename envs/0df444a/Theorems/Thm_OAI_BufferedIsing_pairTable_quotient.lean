-- Prove2me | Theorems.Thm_OAI_BufferedIsing_pairTable_quotient
-- name    : OAI.BufferedIsing.pairTable_quotient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:19:53.367831+00:00
-- url     : https://prove2.me/theorems/e0ca0ba2-f976-4359-966e-788dd16514ab
-- title:
--   Two-site tables of class-constant spin configurations agree with tables on the quotient
-- statement:
--   Let $V$ be a finite set with an equivalence relation $S$, let $\pi:V\to V/S$ be the quotient map, and let $W:\{-1,+1\}^V\to\mathbb{R}$ be an arbitrary function. Call a configuration $\sigma\in\{-1,+1\}^V$ *$S$-compatible* if $\sigma_x=\sigma_y$ whenever $x$ and $y$ are $S$-equivalent. Then for all sites $u,v\in V$ and all values $s,t\in\{-1,+1\}$,
--   $$
--   \sum_{\substack{\sigma\in\{-1,+1\}^V\\ \sigma\ S\text{-compatible}}}\mathbf 1[\sigma_u=s,\ \sigma_v=t]\,W(\sigma)\;=\;\sum_{c\in\{-1,+1\}^{V/S}}\mathbf 1\big[c_{\pi(u)}=s,\ c_{\pi(v)}=t\big]\,W(c\circ\pi).
--   $$
--
--   In words: the two-site table at $(u,v)$ of the weight $W$ restricted to configurations that are constant on equivalence classes coincides with the two-site table at $(\pi(u),\pi(v))$ of the induced weight $c\mapsto W(c\circ\pi)$ on configurations of the quotient. Restricting a spin system to class-constant configurations is therefore the same as identifying the vertices of each class into a single spin; this is how separately contracted terminal blocks become genuine vertices of a contracted Ising model.
--
--   **Formalization Note** Spins are Booleans. The left side is `pairTable (fun σ => if Respects S σ then W σ else 0) u v s t` and the right side is `pairTable (fun c : Quotient S → Bool => W (fun x => c (Quotient.mk S x))) (Quotient.mk S u) (Quotient.mk S v) s t`, where `pairTable W i j s t` sums `W σ` over the configurations with `σ i = s` and `σ j = t`. No assumption on $W$ (sign or positivity) is needed, and $V$ carries a `Fintype` and a `DecidableEq` instance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Contraction.lean#L130-L148

import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction

open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem OAI.BufferedIsing.pairTable_quotient {V : Type*} [Fintype V] [DecidableEq V]
    (S : Setoid V) (W : (V → Bool) → ℝ) (u v : V) (s t : Bool) :
    pairTable (fun σ => if Respects S σ then W σ else 0) u v s t =
      pairTable (fun c : Quotient S → Bool => W (fun x => c (Quotient.mk S x)))
        (Quotient.mk S u) (Quotient.mk S v) s t := by sorry
