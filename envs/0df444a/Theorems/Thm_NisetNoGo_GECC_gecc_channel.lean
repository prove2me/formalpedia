-- Prove2me | Theorems.Thm_NisetNoGo_GECC_gecc_channel
-- name    : NisetNoGo.GECC.gecc_channel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:09.93107+00:00
-- url     : https://prove2.me/theorems/0658c172-6a6a-4f82-bea1-d0910dff92c6
-- title:
--   p. 2 — a Gaussian error-correcting code yields a Gaussian channel
-- statement:
--   Let $T=(M,N)$ be a completely positive single-mode Gaussian channel. For any $n\ge1$, let $S_E$ and $S_D$ be symplectic transformations on $n$ modes. Feed one input mode and $n-1$ vacuum ancillas through $S_E$, apply $T$ independently to every mode, and retain the first output mode after $S_D$. If the resulting matrices are $M_{GC},N_{GC}$, then
--
--   $$T_{GC}=(M_{GC},N_{GC})\text{ is a completely positive Gaussian channel.}$$
--
--   This establishes that every code in Fig. 1 stays within the class of channels to which the degradation measure applies.
-- source:
--   Niset, Fiurášek, Cerf, A No-Go Theorem for Gaussian Quantum Error Correction, arXiv:0811.3128v1, p. 2, paragraph beginning 'Let us now define a Gaussian Error-Correcting Code' and Fig. 1

import Mathlib
import Definitions.Def_NisetNoGo_GECC_Setup

open QAlgorithms.Papers.Independent.Frontier30.P13

namespace NisetNoGo.GECC

theorem gecc_channel (n : ℕ) [NeZero n]
    (M N : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ)
    (SE SD : Matrix (ModeQuadrature (Fin n)) (ModeQuadrature (Fin n)) ℝ)
    (hT : IsCPChannel M N) (hE : IsSymplecticMat SE)
    (hD : IsSymplecticMat SD) :
    IsCPChannel (geccM n M SE SD) (geccN n M N SE SD) := by sorry

end NisetNoGo.GECC
