-- Prove2me | Theorems.Thm_LpBallVI_Affine_theorem_2_2
-- name    : LpBallVI.Affine.theorem_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:11:29.317829+00:00
-- url     : https://prove2.me/theorems/67d81fe5-5b5d-4a0f-9069-a9773b9a443e
-- title:
--   Theorem 2.2 (Deligkas–Fearnley–Hollender–Melissourgos 2024) — PureCircuit is PPAD-complete
-- statement:
--   Let **PureCircuit** be the search problem whose instances are well-formed circuits of NOR gates $w = \mathrm{NOR}(u,v)$ and PURIFY gates $(v,w) = \mathrm{PURIFY}(u)$ on $n$ nodes, and whose solutions are assignments $g : V \to \{0, 1, \bot\}$ satisfying every gate's rule. Then
--   $$\text{PureCircuit is PPAD-complete:}\quad \text{PureCircuit} \in \mathrm{PPAD} \text{ and every PPAD problem reduces to it.}$$
--   This cited result (Deligkas, Fearnley, Hollender, Melissourgos, 2024) is the source of the paper's hardness reduction.
--
--   Differences from the source:
--   - encoding: a PureCircuit instance and its solutions → binary codes: n, the number of gates, each gate as a type bit and three node indices in self-delimiting binary; 2 bits per node value; reason: a concrete code of the search problem
--   - encoding: PPAD (search problems reducible to End-of-Line), PPAD-hard/-complete → QuasiStrictNE.PPAD / CEPolytopeHard.PPADHard / QuasiStrictNE.PPADComplete: total problems with a polynomial-time Levin search reduction to End-of-Line, hardness by such reductions from every PPAD problem; reason: the platform's published PPAD layer; no answer-length bound, as on p. 13
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 13, Theorem 2.2

import Mathlib
import Definitions.Def_QuasiStrictNE_PPADComplete
import Definitions.Def_LpBallVI_Affine_PureCircuit

namespace LpBallVI.Affine

/-- **Theorem 2.2** (Deligkas–Fearnley–Hollender–Melissourgos 2024; Anagnostides–Panageas–Yan,
arXiv:2611.04151, p. 13): finding a solution to `PureCircuit` is PPAD-complete. -/
theorem theorem_2_2 : QuasiStrictNE.PPADComplete PureCircuit := by sorry

end LpBallVI.Affine
