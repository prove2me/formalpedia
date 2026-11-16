-- Prove2me | Theorems.Thm_GeoQAC_Supplement_theorem_A_1
-- name    : GeoQAC.Supplement.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:29:15.036818+00:00
-- url     : https://prove2.me/theorems/b57532c9-180b-4f96-b801-d77c63de714b
-- title:
--   Theorem A.1 — columnwise MPS bond dimension $2^{dw}$ of narrow 2D-QAC outputs
-- statement:
--   1. Let $C$ be a depth-$d$ $[w,h]$-2D-QAC circuit and $\bigotimes_v|\varphi_v\rangle$ a product of one-qubit unit vectors. Then for every column cut $0<j<h$ the output $C\bigotimes_v|\varphi_v\rangle$ has Schmidt rank at most $2^{dw}$ across the cut; that is, it has a columnwise MPS representation of bond dimension at most $2^{dw}$.
--   2. If $C$ computes $f$ exactly from product ancillas (inputs and output anywhere), then the phase state $|\chi_f\rangle|0^a\rangle$, with $|\chi_f\rangle=2^{-n/2}\sum_xi^{f(x)}|x\rangle$ on the input qubits and $|0\rangle$ on every other qubit, has Schmidt rank at most $2^{2dw}$ across every column cut.
--
--   This places the functions computed by narrow constant-depth circuits in a tensor-train model with small bond dimension, the basis of the learning bound of Theorem A.4.
--
--   Differences from the source:
--   - encoding: columnwise MPS bond dimension at most χ → Schmidt rank at most χ across every column cut 0 < j < h; reason: the characterization the paper uses (p.37, [Vid03]): the minimal bond dimension at each cut equals the Schmidt rank across it
--   - encoding: decides f exactly from product ancillas → published GeoQAC.ComputesExactly with any product of one-qubit unit vectors; reason: the paper's convention; |0^a⟩ is the special case
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem A.1, p.38

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_ComputesExactly
import Definitions.Def_GeoQAC_phaseState
import Definitions.Def_GeoQAC_Supplement_cutRank
import Definitions.Def_GeoQAC_Supplement_ComputesWithProb

namespace GeoQAC.Supplement

open GeoQAC Matrix
open DHRUniq (IsUnitVec)

/-- **Theorem A.1** (Dong, Ou, Yao, arXiv:2604.07178, version of 2026-11-03, p.38). "The output of a
depth-`d`, width-`w` 2D-QAC circuit on a product input has a columnwise MPS representation of bond
dimension at most `2^{dw}`. If the circuit decides `f` exactly from product ancillas, its phase state
`|χ_f⟩|0^a⟩` from (1) has bond dimension at most `2^{2dw}`."

**Formalization Note.**
* Bond dimension at most `χ` is "the Schmidt rank across every column cut is at most `χ`", the
  characterization the paper uses (p.37, [Vid03]); the cut `j` with `0 < j < h` separates the columns
  `< j` from the columns `≥ j` (`cutRank`). For `h ≤ 1` there is no cut.
* First clause: every product input `⊗_v φ_v` of one-qubit unit vectors.
* Second clause: `C` computes `f` exactly from product ancillas (published `GeoQAC.ComputesExactly`,
  inputs and output anywhere); `|χ_f⟩|0^a⟩` is the published `GeoQAC.phaseState f` on the input
  qubits tensored with `|0⟩` on every other qubit (`embedInput` with `ket0`). -/
theorem theorem_A_1 :
    (∀ (w h d : ℕ) (C : QACCircuit (Pos w h) d) (φ : Pos w h → Bool → ℂ),
      C.Is2D → (∀ v, IsUnitVec (φ v)) →
      ∀ j : ℕ, 0 < j → j < h → cutRank (C.matrix *ᵥ prodVec φ) j ≤ 2 ^ (d * w)) ∧
    (∀ (w h d n : ℕ) (C : QACCircuit (Pos w h) d) (inp : Fin n ↪ Pos w h)
      (anc : Pos w h → Bool → ℂ) (out : Pos w h) (f : (Fin n → Bool) → Bool),
      C.Is2D → ComputesExactly C inp anc out f →
      ∀ j : ℕ, 0 < j → j < h →
        cutRank (embedInput inp (fun _ => ket0) (phaseState f)) j ≤ 2 ^ (2 * d * w)) := by sorry

end GeoQAC.Supplement
