-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RationalInverse_Native_current_correct
-- name    : InfoLossLAR.WorstCase.RationalInverse.Native.current_correct
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T06:01:10.740093+00:00
-- url     : https://prove2.me/theorems/fdebc4fe-f54e-47d1-b7fd-d4199115a4a9
-- title:
--   Exact inverse-transpose coordinates from a variable-dimensional integer basis
-- statement:
--   For every nonsingular integer matrix $B$ of dimension $n$, the row-major rational matrix returned by the native basis algorithm is exactly $B^{-\mathsf T}$. More explicitly, the returned entry in row $i$, column $j$ is the $i$th Cramer coordinate for $B^{\mathsf T}x=e_j$, divided by $\det B$. This identifies the vectors used to encode fine-lattice queries with the exact dual basis in every dimension.
-- source:
--   InfoLossLAR formalization of physical Fourier sampling from a shared bounded-distance decoder. https://prove2.me/theorems/d106aba4-0ad7-4239-9c6b-4a9dc8c9ebc4

import Definitions.Def_InfoLossLAR_ReciprocallyScaledGaussianSource
set_option autoImplicit false

namespace InfoLossLAR.WorstCase.RationalInverse.Native
theorem current_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
  current (inputRows B) = List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin n =>
    (Matrix.cramer B.transpose (Pi.single j 1) i : ℚ)/(B.det : ℚ))) := by sorry
end InfoLossLAR.WorstCase.RationalInverse.Native
