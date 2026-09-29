-- Prove2me | Theorems.Thm_HarelTarjan_SymOrder_lemma4_nca_height_xor
-- name    : HarelTarjan.SymOrder.lemma4_nca_height_xor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:47:59.830088+00:00
-- url     : https://prove2.me/theorems/05ed0bf0-9ffd-4ee0-b4e9-a46290d642c2
-- title:
--   Lemma 4 — the nca of unrelated $v, w$ has height $\lfloor\lg(\mathrm{sym}(v)\oplus\mathrm{sym}(w))\rfloor$
-- statement:
--   Let $T$ be the complete binary tree of depth $d$, numbered in symmetric order. If $v$ and $w$ are two unrelated vertices (neither is an ancestor of the other), the height of the nearest common ancestor of $v$ and $w$ is
--   $$h(\operatorname{nca}(v,w)) = \left\lfloor \lg\left(\mathrm{sym}(v) \oplus \mathrm{sym}(w)\right) \right\rfloor,$$
--   where $i \oplus j$ is the integer whose binary representation is the bitwise exclusive or of the binary representations of $i$ and $j$.
--
--   Lemma 4 is the third case of the nca depth algorithm. The hypothesis that $v$ and $w$ are unrelated cannot be dropped: when $v$ is a proper ancestor of $w$, the formula can give a height smaller than $h(v)$.
--
--   **Formalization Note** $\oplus$ is `^^^` on $\mathbb N$ and $\lfloor \lg x \rfloor$ is `Nat.log 2 x`; they agree because unrelated vertices have distinct numbers, so the exclusive or is at least $1$.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 342, Lemma 4

import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym

namespace HarelTarjan.SymOrder

/-- Lemma 4 (p. 342): if `v` and `w` are two unrelated vertices, the height of the nearest common
ancestor of `v` and `w` is `⌊lg (sym(v) ⊕ sym(w))⌋`, where `⊕` is bitwise exclusive or
(`^^^` on `ℕ`) and `⌊lg x⌋ = Nat.log 2 x` for `x ≥ 1`. -/
theorem lemma4_nca_height_xor {d : ℕ} (v w : Vertex d) (hvw : Unrelated v w) :
    height (nca v w) = Nat.log 2 (sym v ^^^ sym w) := by sorry

end HarelTarjan.SymOrder
