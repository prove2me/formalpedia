-- Prove2me | Theorems.Thm_GL2QFT_Circuits_nonHardRouting_uniform
-- name    : GL2QFT.Circuits.nonHardRouting_uniform
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T04:03:16.118944+00:00
-- url     : https://prove2.me/theorems/05ee7b95-edc4-4ca0-b81e-8a5a1f131d66
-- title:
--   Uniform input and output routing for the non-hard total A-block
-- statement:
--   For $q>2$, both routing maps around the non-hard local gates have uniform reversible Clifford+$T$ implementations. The input map retains the source register and initializes the clean two-level wire. The output map reversibly computes the block family and character comparisons and writes the determinant, Steinberg, or sorted principal-series label while restoring all work registers to zero. These are the character comparisons and relabeling operations used in the proof of Theorem 6.14.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, arXiv:2608.28573, §6.4.4, equations (128)–(139), pp.45–46, and Theorem 6.14, p.47 (PDF p.48).

import Definitions.Def_GL2QFT_Circuits_NonHardStages

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

theorem GL2QFT.Circuits.nonHardRouting_uniform :
    UniformlyImplementsOn (fun D => 2 < D.q)
      (fun D (x : InRegNonHard D) => inCodeA D x.1)
      (fun D => nonHardMidCode D) (fun D => nonHardPrepare D) ∧
    UniformlyImplementsOn (fun D => 2 < D.q)
      (fun D => nonHardMidCode D)
      (fun D (y : OutRegNonHard D) => outCodeA D y.1)
      (fun D => nonHardFinish D) := by sorry
