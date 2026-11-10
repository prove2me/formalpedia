-- Prove2me | Theorems.Thm_HGASUndecidable_Main_lemma_6_1
-- name    : HGASUndecidable.Main.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:14:35.936493+00:00
-- url     : https://prove2.me/theorems/802b45e5-9764-437b-9114-06370a183bf6
-- title:
--   Lemma 6.1 — Degree raising and dimension padding preserving both stability notions
-- statement:
--   Lemma 6.1 (Degree raising and dimension padding). Let H : R^m → R^m be a homogeneous polynomial vector field of degree three, let j ≥ 0, and let n ≥ m. For (x, z) ∈ R^m × R^{n−m}, define Ĥ(x, z) = (|x|² + |z|²)^j (H(x), −z_1³, …, −z_{n−m}³). (6.1) Then Ĥ is a homogeneous polynomial vector field of degree 3 + 2j. Furthermore, its origin is GAS if and only if the origin of H is GAS, and Lyapunov stable if and only if the origin of H is Lyapunov stable.
--
--   Differences from the source:
--   - encoding: Euclidean spaces with coordinates numbered from one → State n = EuclideanSpace ℝ (Fin n), with coordinates numbered from zero; reason: the coordinate identification preserves the Euclidean norm and every instance
--   - encoding: unique maximal solutions, with existence for all forward times included in stability → HasDerivWithinAt on [0,∞), explicit forward existence, and convergence of every forward solution; reason: polynomial fields are locally Lipschitz, so uniqueness and continuation make these formulations equivalent
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Lemma 6.1, printed p. 35 (PDF 37)

import Definitions.Def_HGASUndecidable_Main_Dynamics

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem lemma_6_1 {m n : ℕ} (hmn : m ≤ n) (j : ℕ)
    (H : State m → State m) (hH : PolynomialField H) (hh : Homogeneous 3 H) :
    PolynomialField (padding hmn j H) ∧ Homogeneous (3+2*j) (padding hmn j H) ∧
    (GAS (padding hmn j H) ↔ GAS H) ∧
    (LyapunovStable (padding hmn j H) ↔ LyapunovStable H) := by sorry

end HGASUndecidable.Main
