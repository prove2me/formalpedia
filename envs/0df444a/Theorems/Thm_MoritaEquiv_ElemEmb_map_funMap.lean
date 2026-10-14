-- Prove2me | Theorems.Thm_MoritaEquiv_ElemEmb_map_funMap
-- name    : MoritaEquiv.ElemEmb.map_funMap
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-12T19:53:00.358702+00:00
-- url     : https://prove2.me/theorems/5e0e3496-f7a9-4618-84d3-b5c96fd29aed
-- title:
--   Elementary embeddings commute with function symbols
-- statement:
--   Let $L$ be a many-sorted signature and let $h : M \to N$ be an elementary embedding of $L$-structures (a sortwise family of maps $h_s : M_s \to N_s$ preserving and reflecting the satisfaction of every formula). Then $h$ commutes with the interpretation of every function symbol: for each $f : s_0 \times \dots \times s_{m-1} \to s$ in $L$ and all $x_j \in M_{s_j}$,
--   $$h_s\big(f^M(x_0,\dots,x_{m-1})\big) = f^N\big(h_{s_0}(x_0),\dots,h_{s_{m-1}}(x_{m-1})\big).$$
--   Constants are the case $m = 0$. This is the basic fact that elementary embeddings are in particular homomorphisms of the underlying many-sorted structures.
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675 (arXiv v1), §4.1 (explicit definitions of new sorts) and §5 (proof of Proposition 5.2)

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- Elementary embeddings commute with the interpretations of function symbols. -/
theorem ElemEmb.map_funMap {L : Sig} {M N : Str L} (h : ElemEmb M N) {m : ℕ} {dom : Fin m → L.Srt}
    {s : L.Srt} (f : L.Func m dom s) (xs : (j : Fin m) → M.carrier (dom j)) :
    h.toFun s (M.funMap f xs) = N.funMap f (fun j => h.toFun (dom j) (xs j)) := by sorry

end MoritaEquiv
