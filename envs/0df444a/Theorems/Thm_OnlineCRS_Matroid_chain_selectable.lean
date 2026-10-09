-- Prove2me | Theorems.Thm_OnlineCRS_Matroid_chain_selectable
-- name    : OnlineCRS.Matroid.chain_selectable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:23:44.09246+00:00
-- url     : https://prove2.me/theorems/2a62c55c-f865-4bdc-8487-7bf334205c7b
-- title:
--   §2.1, p. 10 — characterization of selectability in a chain layer
-- statement:
--   Fix a strictly descending chain $N=N_0\supsetneq\cdots\supsetneq N_\ell=\varnothing$, a layer index $i<\ell$, an element $e\in N_i\setminus N_{i+1}$, and an active set $A$. The element $e$ is selectable from $A$ for the chain family exactly when
--   $$e\notin\operatorname{span}_{(M/N_{i+1})|N_i}\bigl((A\cap(N_i\setminus N_{i+1}))\setminus\{e\}\bigr).$$
--
--   Summing this pointwise equivalence over the independently sampled active sets yields the probability identity displayed before equation (2) of the paper.
-- source:
--   arXiv:1508.00142v2, §2.1, p. 10, display before (2)

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Matroid_Construction

open scoped Matroid

namespace OnlineCRS.Matroid

/-- arXiv:1508.00142v2, §2.1, p. 10, display before (2), pointwise form. -/
theorem chain_selectable {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ) (Nch : ℕ → Finset α) (ℓ : ℕ)
    (hstart : Nch 0 = Finset.univ)
    (hstrict : ∀ j < ℓ, Nch (j + 1) ⊂ Nch j)
    (hend : Nch ℓ = ∅)
    (i : ℕ) (hi : i < ℓ) (e : α) (he : e ∈ Nch i \ Nch (i + 1))
    (A : Finset α) :
    Selectable (chainFamily M Nch ℓ) A e ↔
      e ∉ ((M ／ (Nch (i + 1) : Set α)) ↾ (Nch i : Set α)).closure
        ((((A ∩ (Nch i \ Nch (i + 1)) : Finset α)) : Set α) \ {e}) := by sorry

end OnlineCRS.Matroid
