-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_Supplement_binary_atom_bounds
-- name    : MomentAmbiguitySecretary.Secretary.Supplement.binary_atom_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:52:38.385198+00:00
-- url     : https://prove2.me/theorems/efa3fd96-9057-4bc0-908f-ea46e5cc68bc
-- title:
--   Lemma 8.6 (used in the proof of Theorem 3.1) — Common normalization and all three designated-atom bounds
-- statement:
--   For integers $n,B\ge3$, the canonical binary normalization and designated atom weights satisfy
--   $$W\ge n,\qquad p_2\ge\frac1{4n},\qquad p_0\ge1-\frac2n,\qquad q_1\ge1-\frac1{n^2B^2}.$$
--   Here $p_j$ is the even-law mass and $q_j$ the odd-law mass at $x_j$. These are simultaneous quantitative bounds for the constructed pair.
--
--   Differences from the source: none.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Lemma 8.6, PDF/printed p.27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Binary

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- Lemma 8.6, supplied preprint, PDF/printed p.27. -/
theorem binary_atom_bounds (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (n : ℝ) ≤ binaryW n B ∧
    1 / (4 * (n : ℝ)) ≤ binaryP n B 2 ∧
    1 - 2 / (n : ℝ) ≤ binaryP n B 0 ∧
    1 - 1 / ((n : ℝ) ^ 2 * (B : ℝ) ^ 2) ≤ binaryQ n B 1 := by sorry

end MomentAmbiguitySecretary.Secretary.Supplement
