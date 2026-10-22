-- Prove2me | Theorems.Thm_HollandsSanders_CFTBound_xi_norm_le
-- name    : HollandsSanders.CFTBound.xi_norm_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:17.985129+00:00
-- url     : https://prove2.me/theorems/cbacdb9a-b011-48d2-9fdc-3d05a155d5ed
-- title:
--   Proof of Theorem 13, p. 80 — the map Ξ(a) = Δ^{1/4} aΩ has norm ‖Ξ‖ ⩽ 1
-- statement:
--   Let $\mathfrak M$ be a von Neumann algebra on $\mathcal H$ with a cyclic and separating unit vector $\Omega$ and modular operator $\Delta$. For every $a\in\mathfrak M$ the vector $a\Omega$ lies in the domain of $\Delta^{1/4}$ and
--   $$\|\Delta^{1/4}a\Omega\|\leqslant\|a\|.$$
--   That is, the map $\Xi(a)=\Delta^{1/4}a\Omega$ on $\mathfrak M$ has norm $\|\Xi\|\le1$.
--
--   In the proof of Theorem 13 this is applied to $\mathfrak M=\mathfrak A_A$ and the vacuum, to get $\|\Phi^A\|_1\le\|T\|_1\,\|\Xi^A\|\le\|T\|_1$.
--
--   **Formalization Note.** The domain statement is part of the conclusion: the vector $y=\Delta^{1/4}a\Omega$ is asserted to exist as the limit of $\exp(\min(n,\log\Delta)/4)\,a\Omega$.
-- source:
--   Hollands & Sanders, Entanglement measures and their properties in quantum field theory, arXiv:1702.04924v3, p. 80, proof of Theorem 13

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HollandsSanders_CFTBound_Entanglement
open OAI.BoundedRecovery
open scoped InnerProductSpace ENNReal

namespace HollandsSanders.CFTBound

/-- Proof of Theorem 13 (p. 80): the map `Ξ(a) = Δ^{1/4} a Ω` on a von Neumann algebra `M` with
cyclic and separating vector `Ω` and modular operator `Δ` has norm `‖Ξ‖ ⩽ 1`: `a Ω` lies in the
domain of `Δ^{1/4}` and `‖Δ^{1/4} a Ω‖ ⩽ ‖a‖`. -/
theorem xi_norm_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StandardModularData H) (a : H →L[ℂ] H) (ha : a ∈ S.M) :
    ∃ y : H, (a S.xi, y) ∈ quarterGraph S ∧ ‖y‖ ≤ ‖a‖ := by sorry

end HollandsSanders.CFTBound
