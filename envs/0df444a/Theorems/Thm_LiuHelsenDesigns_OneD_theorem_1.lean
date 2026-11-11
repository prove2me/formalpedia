-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_theorem_1
-- name    : LiuHelsenDesigns.OneD.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:08:33.151274+00:00
-- url     : https://prove2.me/theorems/1740bf45-9a95-4e34-8f5f-3d73ede9a6c4
-- title:
--   Theorem 1 — ancilla-free relative-error designs with both resource bounds
-- statement:
--   Fix $0<c<1$. There are positive constants C_D,C_T, a threshold N, and one terminating effective finite-sampling program. For every $n\ge N$, every positive integer k, and every real $0<\varepsilon\le1$ satisfying $k+\log_2(n/\varepsilon)\le cn$, the program’s law ν is implemented on exactly n wires of one open nearest-neighbor line, with no ancillary qubits, and satisfies
--
--   $$
--   (1-\varepsilon)\Phi_H^{(k)}\preceq\Phi_\nu^{(k)}\preceq(1+\varepsilon)\Phi_H^{(k)},\qquad D\le C_D(\log_2(n/\varepsilon)+k\log_2k),\qquad T\le C_Tnk.
--   $$
--
--   Both resource bounds hold for every circuit in the same finite sampling list. The program receives integer ceiling precision; all admissible real errors remain quantified. No divisibility or special-rank hypothesis is imposed.
--
--   Differences from the source:
--   - reading: approximation errors and design order in the standing context → positive integer order and positive errors at most one (local exact blocks also allow zero); reason: the nontrivial precision regime of §2.1 and the surrounding construction
--   - encoding: uniform O(·) and Ω(1) statements → positive constants chosen before every size, order, precision and representation they are uniform over; reason: only Theorem 1 constants and its size threshold may depend on the fixed c
--   - encoding: explicit sampling and finite gate implementation → a halting partial-recursive program returning encoded finite circuit lists, with real errors selecting ceiling binary precision; reason: uniform lists can include multiplicities; no polynomial classical runtime is asserted
--   - encoding: unqualified logarithms inside O(·) resource or overlap bounds → binary logarithms inside bounds with uniform existential leading constants; reason: changing a fixed logarithm base multiplies these terms by a fixed positive factor, absorbed uniformly into the leading constants; explicit log₂ expressions are unchanged
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 3, Theorem 1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_designs

namespace LiuHelsenDesigns.OneD

/-- Theorem 1, pp.3--5: both resources belong to the same effective finite circuit law. -/
theorem theorem_1 : ∀ c : ℝ, 0 < c → c < 1 →
    ∃ (code : Nat.Partrec.Code) (C_D C_T : ℝ) (N : ℕ),
      0 < C_D ∧ 0 < C_T ∧ 1 ≤ N ∧
      (∀ n k p : ℕ, ∃ cs : List Circuit, ProgramOutputs code n k p cs) ∧
      ∀ n : ℕ, N ≤ n → ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        (k : ℝ) + Real.logb 2 (n / ε) ≤ c * n →
        ∃ cs : List Circuit, ProgramOutputs code n k (precision ε) cs ∧ cs ≠ [] ∧
          RelativeDesign (circuitLaw n cs) k ε ∧
          ∀ C ∈ cs, LegalCircuit n C ∧ ElementaryCircuit C ∧
            (depth C : ℝ) ≤ C_D * (Real.logb 2 (n / ε) + k * Real.logb 2 k) ∧
            (tCount C : ℝ) ≤ C_T * n * k := by sorry

end LiuHelsenDesigns.OneD
