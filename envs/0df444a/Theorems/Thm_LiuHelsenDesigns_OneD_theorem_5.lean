-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_theorem_5
-- name    : LiuHelsenDesigns.OneD.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:10:48.379887+00:00
-- url     : https://prove2.me/theorems/cd785000-d2e2-4035-9cf9-2d459967f73d
-- title:
--   Theorem 5 — constant-depth CPZPC laws and design depth
-- statement:
--   There are uniform positive constants c₀, Δ, C_L and C_D, fixed positive integers r_C,r_P, and an effective choice of local Clifford and permutation generator sets. On n qubits use the actual independent convolution law $\widetilde\nu=\nu_{Cl}^{*r_C}*\nu_P^{*r_P}*\delta_Z*\nu_P^{*r_P}*\nu_{Cl}^{*r_C}$. Every sample has uniformly constant elementary nearest-neighbor depth. For $k\ge1$ and $k\le c_0 2^{n/6.1}$,
--
--   $$
--   g(\widetilde\nu,k)\le1-\Delta,\qquad\Delta\ge\tfrac12,\qquad L=O(nk+\log(1/\varepsilon)),\qquad D_{1D}=O(nk+\log(1/\varepsilon)).
--   $$
--
--   The iteration statement includes every length above a sufficient uniform threshold and a choice of length and elementary implementation with the displayed total-depth bound. The same law supplies the gap and design conclusions.
--
--   Differences from the source:
--   - reading: approximation errors and design order in the standing context → positive integer order and positive errors at most one (local exact blocks also allow zero); reason: the nontrivial precision regime of §2.1 and the surrounding construction
--   - encoding: uniform O(·) and Ω(1) statements → positive constants chosen before every size, order, precision and representation they are uniform over; reason: only Theorem 1 constants and its size threshold may depend on the fixed c
--   - reading: a sufficient iteration count written L=O(·) → all integer lengths above a uniform sufficient threshold, plus a bounded sufficient choice in Theorem 5; reason: an arbitrary small length satisfying an upper big-O bound is not a mixing guarantee
--   - encoding: explicit sampling and finite gate implementation → a halting partial-recursive program returning encoded finite circuit lists, with real errors selecting ceiling binary precision; reason: uniform lists can include multiplicities; no polynomial classical runtime is asserted
--   - encoding: unqualified logarithms inside O(·) resource or overlap bounds → binary logarithms inside bounds with uniform existential leading constants; reason: changing a fixed logarithm base multiplies these terms by a fixed positive factor, absorbed uniformly into the leading constants; explicit log₂ expressions are unchanged
--   - generalization: a constant Δ > 0; samples realizable by nearest-neighbor Clifford and permutation (NOT/CNOT/Toffoli) circuits of depth O(1) → Δ ≥ 1/2; samples realized by elementary Clifford+T nearest-neighbor circuits of bounded depth; generator lists output by halting programs; reason: Eq. (172) of the proof gives Δ ≥ 1/2; a Toffoli on three adjacent wires has an exact constant-depth nearest-neighbor Clifford+T circuit; both specialize to the source statement
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 28, Theorem 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_localLaws

namespace LiuHelsenDesigns.OneD
open MeasureTheory
theorem theorem_5 : ∃ (codeC codeP : Nat.Partrec.Code) (c₀ Δ C_L C_D : ℝ) (D rC rP : ℕ),
    0 < c₀ ∧ (1/2 : ℝ) ≤ Δ ∧ Δ ≤ 1 ∧ 0 < C_L ∧ 0 < C_D ∧
    1 ≤ rC ∧ 1 ≤ rP ∧
    ∀ n : ℕ, 1 ≤ n → ∃ S : Finset (Cl n), ∃ P : Finset (Equiv.Perm (Basis n)),
      S.Nonempty ∧ P.Nonempty ∧
      (∃ csC csP : List Circuit, ProgramOutputs codeC n 0 0 csC ∧
        ProgramOutputs codeP n 0 0 csP ∧ ImplementsClSet csC S ∧ ImplementsPermSet csP P ∧
        (∀ C ∈ csC, depth C ≤ D) ∧ (∀ C ∈ csP, depth C ≤ D)) ∧
      (∀ᵐ U ∂cpzpc n S P rC rP, ∃ C : Circuit,
        LegalCircuit n C ∧ ElementaryCircuit C ∧ circuitMatrix n C = U ∧ depth C ≤ D) ∧
      ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ c₀ * Real.rpow 2 ((n : ℝ)/6.1) →
        IsUnitaryLaw (cpzpc n S P rC rP) ∧
        essentialNorm (cpzpc n S P rC rP) k ≤ 1-Δ ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          (∀ L : ℕ, C_L * ((n : ℝ)*k + Real.logb 2 (1/ε)) ≤ L →
            RelativeDesign (powerLaw (cpzpc n S P rC rP) L) k ε) ∧
          (∃ L : ℕ, L ≤ C_L * ((n : ℝ)*k + Real.logb 2 (1/ε)) + 1 ∧
            RelativeDesign (powerLaw (cpzpc n S P rC rP) L) k ε ∧
            ∀ᵐ U ∂powerLaw (cpzpc n S P rC rP) L, ∃ C : Circuit,
              LegalCircuit n C ∧ ElementaryCircuit C ∧ circuitMatrix n C = U ∧
              (depth C : ℝ) ≤ C_D * ((n : ℝ)*k + Real.logb 2 (1/ε))) := by sorry
end LiuHelsenDesigns.OneD
