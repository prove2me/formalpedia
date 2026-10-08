-- Prove2me | Theorems.Thm_MaxPressure_StrictLeontief_off_buffer_R_nonpos
-- name    : MaxPressure.StrictLeontief.off_buffer_R_nonpos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:55:44.889905+00:00
-- url     : https://prove2.me/theorems/f4d7d3e6-14b0-406d-b5f3-19b091a7027f
-- title:
--   §6.1, proof of Theorem 6, p. 204 — B_ji = 0 and R_ij ≤ 0 for i ≠ i(j)
-- statement:
--   Consider a strict Leontief network satisfying the standing assumptions of §2. Each activity $j$ processes exactly one buffer $i(j)$: an internal buffer if $j$ is a service activity, Buffer $0$ if $j$ is an input activity. Then
--   $$B_{ji}=0\quad\text{and}\quad R_{ij}\le 0\qquad\text{for every } i\in\mathcal I \text{ and } j\in\mathcal J \text{ with } i\neq i(j).$$
--   For an input activity this holds for every internal buffer $i$.
--
--   So in a strict Leontief network an activity consumes material only from its own buffer and can only produce material in the others; this sign pattern is what lets zeroing the activities of empty buffers never decrease the pressure.
--
--   **Formalization Note** $i(j)$ is written relationally: for a service activity, for every internal $i_0$ with $B_{j i_0}=1$ and every internal $i\ne i_0$; for an input activity, for every internal $i$.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 204, §6.1, proof of Theorem 6, sentences 1–3

import Mathlib
import Definitions.Def_MaxPressure_StrictLeontief_Network

namespace MaxPressure.StrictLeontief

/-- Proof of Theorem 6, p. 204: in a strict Leontief network every activity `j` has exactly
one buffer `i(j)`, and `B_{ji} = 0`, `R_{ij} ≤ 0` for every internal buffer `i ≠ i(j)`.
For a service activity `i(j)` is internal; for an input activity `i(j) = 0`, so the claim
covers every internal buffer. -/
theorem off_buffer_R_nonpos {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hSL : IsStrictLeontief N) :
    (∀ j, IsServiceActivity N j → ∀ i₀ : Fin I, N.B j i₀.succ = 1 →
      ∀ i : Fin I, i ≠ i₀ → N.B j i.succ = 0 ∧ R N i j ≤ 0) ∧
    (∀ j, IsInputActivity N j → ∀ i : Fin I, N.B j i.succ = 0 ∧ R N i j ≤ 0) := by sorry

end MaxPressure.StrictLeontief
