-- Prove2me | Theorems.Thm_LowRankShifts_MatPoly_corollary_2_9
-- name    : LowRankShifts.MatPoly.corollary_2_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:58:25.791236+00:00
-- url     : https://prove2.me/theorems/6f47560c-d03c-42fc-adc6-697fbc104162
-- title:
--   Corollary 2.9 — the low-rank-shift difference with transposes and one shared U in O(rn²sd2^d) time
-- statement:
--   Let $F$ be any field. There is a universal constant $C$ and one deterministic program of the machine `LowRankShifts_MatPoly_Machine` taking as input a polynomial $P\in F\langle X_1,\dots,X_\ell,\cdot^T\rangle$ consisting of $s$ (distinct) monomials each of degree at most $d$, matrices $A=(A_1,\dots,A_\ell)\in(F^{n\times n})^\ell$, $U\in F^{n\times r}$ and $V=(V_1,\dots,V_\ell)\in(F^{n\times r})^\ell$, which halts after at most $C\,rn^2sd\,2^d+C$ operations with output
--
--   $$\Delta_P(A,U,V)=P(A+UV^T)-P(A)=P(A_1+UV_1^T,\dots,A_\ell+UV_\ell^T)-P(A_1,\dots,A_\ell).$$
--
--   This is the form used in line 4 of the amplifier (Algorithm 1) behind Theorem 3.5.
--
--   **Formalization Note.** `sharedShiftInput P A U V` stores $A$'s, $U$, $V$'s (row-major) and the coefficients of $P$ as field blocks, the words of $P$ in the index memory, and $n,r,\ell,s$ in index registers $0$–$3$; the output is the $n\times n$ matrix read row-major from the address designated by `haltOut`.
--
--   Differences from the source:
--   - encoding: an algorithm (deterministic) for any field F → a `Program` with no `sample` and no `query` instruction (`IsDeterministic`), run under an arbitrary sampling law and an arbitrary oracle, which it never consults; every run halts and outputs Δ; reason: the paper names no machine; without sampling and queries the run is the same deterministic computation for every field, infinite fields included
--   - encoding: input P, A, U, V; output Δ_P(A, U, V) → `sharedShiftInput P A U V`: A_1..A_ℓ, U, V_1..V_ℓ row-major and the coefficients of P as field blocks, the words of P in the index memory, n, r, ℓ, s in index registers 0–3; the output is the n × n matrix read row-major from the address designated by `haltOut`; reason: a fixed input/output convention of the machine
--   - encoding: P consisting of s monomials each with degree at most d → `P : MatPolynomial F ℓ` with pairwise distinct words (`(P.map Prod.snd).Nodup`); s = `size P`, d = `degree P` (the maximal word length); reason: the paper's list representation (p. 8) of a polynomial consisting of s monomials: the monomials of a polynomial are distinct, so the words of its list are pairwise distinct (without this, a list of s copies of a constant has d = 0 and a time bound of C, yet Δ depends on whether one unread word is empty, so no program meets it); the bound increases with d, so stating it at the least admissible d is equivalent to stating it for every d bounding the degrees
--   - generalization: monomials with nonzero coefficients → the list's coefficients may be 0; reason: a monomial of a polynomial has a nonzero coefficient; a zero-coefficient entry changes neither P nor Δ_P and only increases s, hence the bound, so the statement specializes to the paper's
--   - encoding: any (finite) field F → any field `F : Type u` (with `DecidableEq F`, which every type has classically); reason: Lean's universe and decidability conventions; no field is excluded
--   - reading: runs in time O(rn^2sd2^d) → every run halts with ops ≤ C·r·n²·s·d·2^d + C, the constant fixed before every other quantity (field, polynomial, dimensions, inputs, oracle); reason: worst-case reading of O(·) as C·f + C on every run; time counts field operations at unit cost (p. 8), so the constant does not depend on the field
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), p. 12 (PDF 15), Corollary 2.9

import Mathlib
import Definitions.Def_LowRankShifts_MatPoly_MatPoly
import Definitions.Def_LowRankShifts_MatPoly_Machine
import Definitions.Def_LowRankShifts_MatPoly_Inputs

open Matrix

set_option autoImplicit false

universe u

namespace LowRankShifts.MatPoly

/-- Corollary 2.9 (p. 12): for any field `F`, one deterministic program that takes as input a
matrix polynomial `P` with transposes, with `s` monomials (pairwise distinct words) of degree at most `d`, matrices
`A ∈ (F^{n×n})^ℓ`, `U ∈ F^{n×r}` and `V ∈ (F^{n×r})^ℓ`, and outputs
`Δ_P(A, U, V) = P(A_1 + UV_1ᵀ, …, A_ℓ + UV_ℓᵀ) − P(A_1, …, A_ℓ)` within
`C·r·n²·s·d·2^d + C` operations. -/
theorem corollary_2_9 :
    ∃ C : ℝ, ∀ (F : Type u) [Field F] [DecidableEq F],
      ∃ B : Program F, B.IsDeterministic ∧
        ∀ (ℓ n r : ℕ) (P : MatPolynomial F ℓ), (P.map Prod.snd).Nodup →
        ∀ (A : Fin ℓ → Matrix (Fin n) (Fin n) F)
          (U : Matrix (Fin n) (Fin r) F) (V : Fin ℓ → Matrix (Fin n) (Fin r) F)
          (samp : PMF F) (O : VecOracle F 0 0),
          let T : ℝ := C * (r : ℝ) * (n : ℝ) ^ 2 * (size P : ℝ) * (degree P : ℝ) * 2 ^ degree P + C
          RunsWithin samp O B (sharedShiftInput P A U V) T 0 ∧
          ∀ σ ∈ (finalLaw samp O B (sharedShiftInput P A U V) T 0).support,
            outMat n n σ = some (eval P (fun i => A i + U * (V i)ᵀ) - eval P A) := by sorry

end LowRankShifts.MatPoly
