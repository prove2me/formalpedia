-- Prove2me | Theorems.Thm_NadlerCLS_decoder_of_clib
-- name    : NadlerCLS.decoder_of_clib
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-26T23:38:15.242662+00:00
-- url     : https://prove2.me/theorems/818d1eb4-988d-470c-b734-23c73af7c01f
-- title:
--   Polynomial-time decoders from multitape programs
-- statement:
--   Decoders of search reductions may be programmed on multitape machines.
--
--   Let $h$ be a map from pairs of binary words to binary words that is computable in polynomial time by a multitape Turing machine, with the pair $(s,t)$ given as the self-delimiting code of Complexitylib (`encPair encBits encBits`). Then there is a map $g$ on words over the pair alphabet $\{0_A,1_A,\#,0_B,1_B\}$, computable in polynomial time by a one-tape Turing machine in Cook's model, such that
--
--   $$g(s\#t)=h(s,t)\qquad\text{for all binary words } s,t .$$
--
--   Here $s\#t$ is the word whose letters are those of $s$ tagged $A$, then the separator, then those of $t$ tagged $B$. This is exactly the input of the answer map of a search reduction, so the lemma lets every decoder of this mission be written as an ordinary polynomial-time function of the instance $s$ and the answer $t$.
--
--   **Formalization Note** Polynomial time on the multitape side is Complexitylib's `Turing.MultiTapeTM.ComputableInPolyTime`; on the one-tape side it is `CookPvsNP.PolyTimeComputable`, and the pair alphabet is `Option (Bool ⊕ Bool)` as in the public `SearchReduces`.
-- source:
--   Formalization infrastructure for the decoders of Xiong–Vlatakis-Gkaragkounis, arXiv:2609.14101v4, Appendix C (p.38: "every part of the reduction is computable in polynomial time"; p.39: "Every decoder uses polynomially many rational operations"); one-tape machines of S. Cook, The P versus NP problem (Clay Mathematics Institute), Appendix; multitape machines of Complexitylib.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pair
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List

set_option autoImplicit false

namespace NadlerCLS

open Turing.MultiTapeTM

theorem decoder_of_clib (h : List Bool × List Bool → List Bool)
    (hh : ComputableInPolyTime h (encPair encBits encBits) encBits) :
    ∃ g : List (Option (Bool ⊕ Bool)) → List Bool, CookPvsNP.PolyTimeComputable g ∧
      ∀ s t : List Bool, g (s.map (some ∘ Sum.inl) ++ none :: t.map (some ∘ Sum.inr)) = h (s, t) := by sorry

end NadlerCLS
