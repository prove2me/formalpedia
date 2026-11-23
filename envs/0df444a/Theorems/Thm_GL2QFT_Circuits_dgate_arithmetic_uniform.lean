-- Prove2me | Theorems.Thm_GL2QFT_Circuits_dgate_arithmetic_uniform
-- name    : GL2QFT.Circuits.dgate_arithmetic_uniform
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:45:15.228291+00:00
-- url     : https://prove2.me/theorems/fae1134e-3131-48f1-b728-67c95e03cda9
-- title:
--   Lemma 6.28: uniform coherent computation and uncomputation for $D_\gamma$
-- statement:
--   On input $|\gamma\rangle|c\rangle$, reversibly compute the clean work label $\delta=\gamma-2\alpha$ for $c=c_\alpha$ (and the zero sentinel for $c=c_\infty$), while applying the sign $\chi_{\gamma-\alpha}(-1)$ and an additional minus sign when $\delta=0$. The second map is its clean uncomputation, applying the inverse sign and returning the work register to its initial state.
--
--   Both operations must be implemented by one uniform polynomial-size family of Clifford+$T$ circuits, with all ancillas clean. This is precisely the reversible character arithmetic preceding and following the Gauss-phase call in Lemma 6.28.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573, Lemma 6.28 (Implementation of D_gamma), p.54: compute b and alpha^{-1}b, apply chi_b(-1), then uncompute both labels.

import Definitions.Def_GL2QFT_Circuits_DgateStages

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem dgate_arithmetic_uniform :
    UniformlyImplementsOn (fun _ => True) (fun D => D.gammaInCode) (fun D => dgateMidCode D)
      (fun D => dgateComputeMat D) ∧
    UniformlyImplementsOn (fun _ => True) (fun D => dgateMidCode D) (fun D => D.gammaInCode)
      (fun D => dgateUncomputeMat D) := by sorry
