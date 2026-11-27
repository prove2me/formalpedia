-- Prove2me | Theorems.Thm_NadlerCLS_binarize_polyTime
-- name    : NadlerCLS.binarize_polyTime
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-26T23:24:25.256036+00:00
-- url     : https://prove2.me/theorems/17d16a23-b87b-4243-a021-81673606580f
-- title:
--   Binary coding of the pair alphabet is polynomial-time
-- statement:
--   Let $\Sigma=\{\#\}\cup\{0_A,1_A\}\cup\{0_B,1_B\}$ be the three-part alphabet over which a pair of binary words $(s,t)$ is written as $s\#t$ (letters of $s$ tagged $A$, letters of $t$ tagged $B$, and the separator $\#$). Code each letter by a binary word,
--
--   $$\#\mapsto 0,\qquad b_A\mapsto 1\,0\,b,\qquad b_B\mapsto 1\,1\,b\qquad(b\in\{0,1\}),$$
--
--   and extend the code letterwise to words: $\mathrm{bin}(c_1c_2\cdots c_m)=\mathrm{code}(c_1)\,\mathrm{code}(c_2)\cdots\mathrm{code}(c_m)$. Then the map $\mathrm{bin}:\Sigma^*\to\{0,1\}^*$ is computable in polynomial time by a deterministic one-tape Turing machine.
--
--   The code is prefix-free, so $\mathrm{bin}$ is injective. This lemma lets the decoder of a search reduction, which reads the coded pair $s\#t$ over $\Sigma$, be written as a polynomial-time map on binary words composed with $\mathrm{bin}$.
--
--   **Formalization Note** The alphabet is `Option (Bool ⊕ Bool)` with `none` the separator, as in Cook's `checkLang` and in the public `SearchReduces`; polynomial time is `CookPvsNP.PolyTimeComputable`.
-- source:
--   Formalization infrastructure for the decoders of Xiong–Vlatakis-Gkaragkounis, arXiv:2609.14101v4, Appendix C (p.38: "every part of the reduction is computable in polynomial time"; p.39: "Every decoder uses polynomially many rational operations"), in S. Cook's one-tape Turing-machine model (The P versus NP problem, Clay Mathematics Institute, Appendix).

import Mathlib
import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

namespace NadlerCLS

theorem binarize_polyTime : CookPvsNP.PolyTimeComputable (fun x : List (Option (Bool ⊕ Bool)) =>
    x.flatMap (fun c => match c with
      | none => [false]
      | some (Sum.inl b) => [true, false, b]
      | some (Sum.inr b) => [true, true, b])) := by sorry

end NadlerCLS
