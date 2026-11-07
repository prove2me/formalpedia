-- Prove2me | Theorems.Thm_KTUnitary_Synth_lemma_5_7
-- name    : KTUnitary.Synth.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:30:24.187657+00:00
-- url     : https://prove2.me/theorems/dce3d056-873b-401f-929d-c89fc0e115bc
-- title:
--   Lemma 5.7 — column approximation yields global approximation
-- statement:
--   Let $C$ be a matrix on $n+a$ qubits and $U$ a matrix on $n$ qubits. Suppose that for every $x\in\{0,1\}^n$,
--   $$\big\|C|x\rangle|0^a\rangle-(U|x\rangle)|0^a\rangle\big\|\le\frac{\varepsilon}{\sqrt{2^n}} .$$
--   Then for every $n$-qubit state $|\psi\rangle$,
--   $$\big\|C|\psi\rangle|0^a\rangle-(U|\psi\rangle)|0^a\rangle\big\|\le\varepsilon .$$
--
--   Together with Lemma 5.3 it reduces the correctness of an implementation to its action on basis states.
--
--   Differences from the source:
--   - encoding: (n + a)-qubit matrices acting on |ψ⟩|0^a⟩ → matrices over Bits N with n ≤ N, input on the first n wires, ancillas on the last N − n; reason: a qubit-ordering convention; same statement
--   - generalization: C and U are the matrices of the surrounding text (an implementation and a unitary) → C and U arbitrary complex matrices; reason: the lemma states no unitarity and its proof uses none; it specializes to unitary C, U
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Lemma 5.7, p. 18

import Mathlib
import Definitions.Def_KTUnitary_Synth_vecNorm
import Definitions.Def_KTUnitary_Synth_ancPad

open QAlgorithms.Complexity

namespace KTUnitary.Synth

/-- **Lemma 5.7** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Lemma 5.7, p. 18; unitary column approximation yields global
approximation). Suppose that for every `x ∈ {0,1}^n`, `‖C |x⟩|0^a⟩ − (U |x⟩) |0^a⟩‖ ≤ ε/√(2^n)`. Then
for every `n`-qubit `|ψ⟩`, `‖C |ψ⟩|0^a⟩ − (U |ψ⟩) |0^a⟩‖ ≤ ε`.

**Formalization Note** The lemma states no unitarity, so `C` (on `N = n + a` qubits) and `U` (on `n`
qubits) are arbitrary matrices; `|x⟩` is the basis vector `Pi.single x 1`; an `n`-qubit `|ψ⟩` is a
unit vector. -/
theorem lemma_5_7 {n N : ℕ} (h : n ≤ N) (C : Matrix (Bits N) (Bits N) ℂ)
    (U : Matrix (Bits n) (Bits n) ℂ) (ε : ℝ)
    (hx : ∀ x : Bits n, vecNorm (C.mulVec (ancPad h (Pi.single x 1)) -
      ancPad h (U.mulVec (Pi.single x 1))) ≤ ε / Real.sqrt (2 ^ n))
    (ψ : Bits n → ℂ) (hψ : vecNorm ψ = 1) :
    vecNorm (C.mulVec (ancPad h ψ) - ancPad h (U.mulVec ψ)) ≤ ε := by sorry

end KTUnitary.Synth
