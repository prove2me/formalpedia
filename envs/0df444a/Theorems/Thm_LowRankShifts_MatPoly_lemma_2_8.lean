-- Prove2me | Theorems.Thm_LowRankShifts_MatPoly_lemma_2_8
-- name    : LowRankShifts.MatPoly.lemma_2_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:58:17.846+00:00
-- url     : https://prove2.me/theorems/3651a753-bdf4-4a0a-aaf8-2a9ef562ac13
-- title:
--   Lemma 2.8 — the low-rank-shift difference Δ_P(A, U, V) of a transpose-free matrix polynomial in O(rn²sd2^d) time
-- statement:
--   Let $F$ be any field. There is a universal constant $C$ and one deterministic program of the machine `LowRankShifts_MatPoly_Machine` taking as input a non-commutative polynomial $P\in F\langle X_1,\dots,X_\ell\rangle$ (no transposes) consisting of $s$ (distinct) monomials each of degree at most $d$, matrices $A=(A_1,\dots,A_\ell)\in(F^{n\times n})^\ell$, $U=(U_1,\dots,U_\ell)\in(F^{n\times r})^\ell$ and $V=(V_1,\dots,V_\ell)\in(F^{n\times r})^\ell$, which halts after at most $C\,rn^2sd\,2^d+C$ operations with output
--
--   $$\Delta_P(A,U,V)=P(A_1+U_1V_1^T,\dots,A_\ell+U_\ell V_\ell^T)-P(A_1,\dots,A_\ell).$$
--
--   A rank-$r$ shift changes $P$ by a sum of products each containing a factor $U_iV_i^T$, so the difference costs about $r/n$ of a matrix product per monomial; Theorem 3.5 uses this to undo the random shifts it applies.
--
--   **Formalization Note.** `shiftInput P A U V` stores $A$'s, $U$'s, $V$'s (row-major) and the coefficients of $P$ as field blocks, the words of $P$ in the index memory, and $n,r,\ell,s$ in index registers $0$–$3$; the output is the $n\times n$ matrix read row-major from the address designated by `haltOut`. $d$ is the maximal word length of $P$; the words of the list are pairwise distinct, as the monomials of a polynomial are.
--
--   Differences from the source:
--   - encoding: an algorithm (deterministic) for any field F → a `Program` with no `sample` and no `query` instruction (`IsDeterministic`), run under an arbitrary sampling law and an arbitrary oracle, which it never consults; every run halts and outputs Δ; reason: the paper names no machine; without sampling and queries the run is the same deterministic computation for every field, infinite fields included
--   - encoding: input P, A, U, V; output Δ_P(A, U, V) → `shiftInput P A U V`: A_1..A_ℓ, U_1..U_ℓ, V_1..V_ℓ row-major and the coefficients of P as field blocks, the words of P in the index memory, n, r, ℓ, s in index registers 0–3; the output is the n × n matrix read row-major from the address designated by `haltOut`; reason: a fixed input/output convention of the machine
--   - encoding: P ∈ F⟨X_1, …, X_ℓ⟩ consisting of s monomials each with degree at most d → `P : MatPolynomial F ℓ` with `TransposeFree P` and pairwise distinct words (`(P.map Prod.snd).Nodup`); s = `size P`, d = `degree P` (the maximal word length); reason: the paper's list representation (p. 8) of a polynomial consisting of s monomials: the monomials of a polynomial are distinct, so the words of its list are pairwise distinct (without this, a list of s copies of a constant has d = 0 and a time bound of C, yet Δ depends on whether one unread word is empty, so no program meets it); the bound increases with d, so stating it at the least admissible d is equivalent to stating it for every d bounding the degrees
--   - generalization: monomials with nonzero coefficients → the list's coefficients may be 0; reason: a monomial of a polynomial has a nonzero coefficient; a zero-coefficient entry changes neither P nor Δ_P and only increases s, hence the bound, so the statement specializes to the paper's
--   - encoding: any (finite) field F → any field `F : Type u` (with `DecidableEq F`, which every type has classically); reason: Lean's universe and decidability conventions; no field is excluded
--   - reading: runs in time O(rn^2sd2^d) → every run halts with ops ≤ C·r·n²·s·d·2^d + C, the constant fixed before every other quantity (field, polynomial, dimensions, inputs, oracle); reason: worst-case reading of O(·) as C·f + C on every run; time counts field operations at unit cost (p. 8), so the constant does not depend on the field
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), p. 12 (PDF 15), Lemma 2.8

import Mathlib
import Definitions.Def_LowRankShifts_MatPoly_MatPoly
import Definitions.Def_LowRankShifts_MatPoly_Machine
import Definitions.Def_LowRankShifts_MatPoly_Inputs

open Matrix

set_option autoImplicit false

universe u

namespace LowRankShifts.MatPoly

/-- Lemma 2.8 (p. 12): for any field `F`, one deterministic program that takes as input a
transpose-free matrix polynomial `P` with `s` monomials (pairwise distinct words) of degree at most `d`, matrices
`A ∈ (F^{n×n})^ℓ` and `U, V ∈ (F^{n×r})^ℓ`, and outputs
`Δ_P(A, U, V) = P(A_1 + U_1V_1ᵀ, …, A_ℓ + U_ℓV_ℓᵀ) − P(A_1, …, A_ℓ)` within
`C·r·n²·s·d·2^d + C` operations. -/
theorem lemma_2_8 :
    ∃ C : ℝ, ∀ (F : Type u) [Field F] [DecidableEq F],
      ∃ B : Program F, B.IsDeterministic ∧
        ∀ (ℓ n r : ℕ) (P : MatPolynomial F ℓ), TransposeFree P → (P.map Prod.snd).Nodup →
        ∀ (A : Fin ℓ → Matrix (Fin n) (Fin n) F) (U V : Fin ℓ → Matrix (Fin n) (Fin r) F)
          (samp : PMF F) (O : VecOracle F 0 0),
          let T : ℝ := C * (r : ℝ) * (n : ℝ) ^ 2 * (size P : ℝ) * (degree P : ℝ) * 2 ^ degree P + C
          RunsWithin samp O B (shiftInput P A U V) T 0 ∧
          ∀ σ ∈ (finalLaw samp O B (shiftInput P A U V) T 0).support,
            outMat n n σ = some (eval P (fun i => A i + U i * (V i)ᵀ) - eval P A) := by sorry

end LowRankShifts.MatPoly
