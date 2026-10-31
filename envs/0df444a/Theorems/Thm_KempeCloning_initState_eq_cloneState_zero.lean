-- Prove2me | Theorems.Thm_KempeCloning_initState_eq_cloneState_zero
-- name    : KempeCloning.initState_eq_cloneState_zero
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:24:11.20907+00:00
-- url     : https://prove2.me/theorems/d3f14f37-769c-417c-b87a-637ccc157aa3
-- title:
--   Sec. II C, p.5: $|\Psi_{in}\rangle = |\mathcal F_0\rangle$
-- statement:
--   For all $m, N\in\mathbb N$, the initial state (13) is the cloner state (19) with $l = 0$:
--
--   $$|\Psi_{in}\rangle = |m,0,0,0,N\rangle = |\mathcal F_0\rangle .$$
--
--   This is the base case of the paper's induction showing that the evolved state is always a superposition of the states $|\mathcal F_l\rangle$.
--
--   Differences from the source:
--   - reading: "for arbitrary $N$ and $m$" (p.5) → every $m, N\in\mathbb N$, including $m = 0$ and $N = 0$; reason: the page does not exclude these values; the stronger reading is taken, and it specializes to $m, N\ge1$
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II C, paragraph after (20), p.5

import Definitions.Def_KempeCloning_initState
import Definitions.Def_KempeCloning_cloneState

namespace KempeCloning

/-- **The initial state is `|F_0⟩`.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II C, p.5: "To prove that the system is
indeed always in a superposition of the states |F_l⟩ as in Eq. (19) we use induction: The initial
state of the system is |Ψin⟩ = |F0⟩."

For all `m, N`: `|m, 0, 0, 0, N⟩ = |F_0⟩`. -/
theorem initState_eq_cloneState_zero (m N : ℕ) :
    initState m N = cloneState m N 0 := by sorry

end KempeCloning
