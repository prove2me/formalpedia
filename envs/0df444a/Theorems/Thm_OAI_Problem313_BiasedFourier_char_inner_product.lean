-- Prove2me | Theorems.Thm_OAI_Problem313_BiasedFourier_char_inner_product
-- name    : OAI.Problem313.BiasedFourier.char_inner_product
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:48:01.171948+00:00
-- url     : https://prove2.me/theorems/f41e9fde-8c5a-486f-8a74-5136f6eac80e
-- title:
--   Orthonormality of the $p$-biased characters
-- statement:
--   Let $\iota$ be a finite set and $0<p<1$. On $\{0,1\}^\iota$ let $w_p(x)=\prod_ip^{[x_i]}(1-p)^{1-[x_i]}$, $\chi_p(b)=([b]-p)/\sqrt{p(1-p)}$, $\chi_S(x)=\prod_{i\in S}\chi_p(x_i)$ and $\hat g(S)=\sum_xw_p(x)g(x)\chi_S(x)$. Then for all $S,T\subseteq\iota$,
--   $$
--   \sum_xw_p(x)\,\chi_S(x)\chi_T(x)=[S=T] .
--   $$
--
--   So the characters $\chi_S$ form an orthonormal family in $L^2(w_p)$. There are $2^{|\iota|}$ of them, so they form a basis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierOrthogonality.lean#L51-L81

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality

open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
universe u
open scoped BigOperators
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem OAI.Problem313.BiasedFourier.char_inner_product {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (S T : Finset ι) :
    (∑ x : ι → Bool, weight p x * char p S x * char p T x) =
      if S = T then 1 else 0 := by sorry
