-- Prove2me | Theorems.Thm_LinSysAmp_Supplement_theorem_6_1
-- name    : LinSysAmp.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:52:16.711032+00:00
-- url     : https://prove2.me/theorems/dde2af6b-eaf1-44fc-a137-8022607ac19b
-- title:
--   Theorem 6.1 — exact solving of random linear systems from partial agreement (all four clauses)
-- statement:
--   Let $\mathbb F_q$ be a finite field, $n\ge1$, and let $O$ be an algorithm, taking time $T$ per call, such that
--   $$\mathbb E_{M\leftarrow GL_n(\mathbb F_q),\,c\leftarrow\mathbb F_q^n,\,O}\Big[\frac1n\big|\{i\in[n]:O(M,c)_i=(M^{-1}c)_i\}\big|\Big]\ge\gamma,\qquad\gamma=\frac1q+\varepsilon,\ \varepsilon>0. \tag{7}$$
--   There is an algorithm with the following properties.
--
--   1. It makes at most $m$ calls to $O$, where $m=O(\varepsilon^{-2}\log(n/\varepsilon))$, and $m=O(\gamma^{-1}\log(n/\gamma))$ when $q\ge200/\gamma$. It runs in time $O((T+n^2)m)$.
--   2. It never outputs a wrong solution.
--   3. It succeeds with probability at least $7/8$ on input $(M,y)$, where $M\leftarrow GL_n(\mathbb F_q)$ and $y$ is an arbitrary function of $M$.
--
--   Furthermore:
--
--   4. for all $0<\beta,\delta<1/2$, multiplying the bounds on the number of calls and the running time by $O(\log(1/(\beta\delta)))$ gives an algorithm which, for all but a $\beta$ fraction of the matrices $M\in GL_n(\mathbb F_q)$, succeeds with probability at least $1-\delta$ on every right-hand side;
--   5. for all $1\le k\le n$ and $0<\delta<1/2$, there is an algorithm which runs in time $O(((T+n^2)m+n^2k^{\omega-2+o(1)})\log(1/\delta))$ and, for all but a $74q^{-2k}$ fraction of the matrices, succeeds with probability at least $1-\delta$ on every right-hand side;
--   6. for $k=\lceil n^{0.32}\rceil$ the term $n^2k^{\omega-2+o(1)}$ can be replaced by $n^{2+o(1)}$.
--
--   A random vector agrees with the solution on a $1/q$ fraction of coordinates; the theorem says that any algorithm beating this trivial agreement by $\varepsilon$ yields an exact, never-wrong solver.
--
--   **Formalization Note** The algorithms are programs of the supplement's oracle machine with the LINEQ interface (the published machine has room for only two parameters). One function $m=m(n,\varepsilon)$ serves all clauses; $\omega$ is the published `LinSysAmp.omegaAlg`; $o(1)$ is read as "for every $\varepsilon'>0$, with a constant depending on $\varepsilon'$ and the field", as in the published Proposition 4.8.
--
--   Differences from the source:
--   - encoding: m = O(ε⁻² log(n/ε)), and m = O(γ⁻¹ log(n/γ)) when q ≥ 200/γ → m ≤ C(ε⁻² log(n/ε) + 1), and m ≤ C(γ⁻¹ log(n/γ) + 1) when q ≥ 200/γ; reason: m ≥ 1 while ε⁻² log(n/ε) tends to 0 at n = 1 as ε → 1 − 1/q; for n ≥ 3 the + 1 at most doubles the bound
--   - encoding: running time O((T + n²)m), times O(log(1/(βδ))), and O(((T + n²)m + n²k^{ω−2+o(1)}) log(1/δ)) for a time-T oracle → on every run: calls ≤ m (clause 1), C·m·log(1/(βδ)) (clause 4), C′·m·log(1/δ) (clauses 5, 6), field operations ≤ C·n²·m, C·n²·m·log(1/(βδ)), C′(n²m + n²k^{ω−2+ε′})log(1/δ) and C′(n²m + n^{2+ε′})log(1/δ); reason: the oracle's cost T is charged per call, so the two bounds give the printed time bound; the machine counts calls and field operations separately
--   - reading: O(·) bounds with unnamed constants, and the exponents ω − 2 + o(1) and 2 + o(1) → one absolute C, chosen before the field, for clauses 1–4; for clauses 5 and 6, for every ε′ > 0 a program and a constant C′ chosen after the field and ε′; ω = omegaAlg F; reason: the o(1) terms come from fast (rectangular) matrix multiplication over the given field; same reading as the published Proposition 4.8
--   - generalization: the cost (and correctness) guarantees are stated for an oracle with the assumed expected agreement γ → they hold for every oracle; only the success guarantee assumes the expected agreement γ; reason: the reduction's cost never depends on the oracle's quality; the source's instance is the special case
--   - encoding: an algorithm for LINEQ → a program of the supplement's oracle machine with the LINEQ interface (M row-major, then y); reason: the published machine stores only n, k, t; clauses 5 and 6 need three parameters
--   - encoding: n is an integer dimension → 1 ≤ n; reason: §3.1 fixes n ≥ 1 ("For an integer n ≥ 1")
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Theorem 6.1, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_LinSysAmp_Machine
import Definitions.Def_LinSysAmp_lineqSuccess
import Definitions.Def_LinSysAmp_omegaAlg
import Definitions.Def_LinSysAmp_Supplement_OracleMachine
import Definitions.Def_LinSysAmp_Supplement_Problems

set_option autoImplicit false

open Matrix

namespace LinSysAmp.Supplement

universe u

/-- Theorem 6.1 (Exact solving from partial agreement), p.33 (PDF p.35). Couteau, Melissaris,
Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography*,
arXiv:2611.04680 (version held, sha256 af7a90ac…).

"Let O be a time-T algorithm such that
E_{M←GL_n(F_q), c←F_qⁿ, O}[(1/n)·|{i ∈ [n] : O(M, c)_i = (M⁻¹c)_i}|] ≥ γ,   (7)
where γ = 1/q + ε for some ε > 0. There is an algorithm with the following properties.
• It makes at most m calls to O, where m = O(ε⁻² log(n/ε)), and m = O(γ⁻¹ log(n/γ)) when q ≥ 200/γ.
It runs in time O((T + n²)m).
• It never outputs a wrong solution.
• It succeeds with probability at least 7/8 on input (M, y), where M ← GL_n(F_q) and y is an
arbitrary function of M.
Furthermore, for all 0 < β, δ < 1/2, multiplying the bounds on the number of calls and the running
time by O(log(1/(βδ))) gives an algorithm which, for all but a β fraction of the matrices
M ∈ GL_n(F_q), succeeds with probability at least 1 − δ on every right-hand side. Similarly, for all
1 ≤ k ≤ n and 0 < δ < 1/2, there is an algorithm which runs in time
O(((T + n²)m + n²k^{ω−2+o(1)}) log(1/δ)) and, for all but a 74q^{−2k} fraction of the matrices
M ∈ GL_n(F_q), succeeds with probability at least 1 − δ on every right-hand side. For k = ⌈n^{0.32}⌉,
the term n²k^{ω−2+o(1)} can be replaced by n^{2+o(1)} (Section 4.3)."

**Formalization Note.**
* *Machine.* Every algorithm is a program of `LinSysAmp.Supplement.OracleMachine` with the LINEQ
  interface `lineqIface O` (each call reads an `n × n` matrix and a right-hand side and writes the
  `n` coordinates of the answer). The published `LinSysAmp.Machine` has room for only two numeric
  parameters, and the third and fourth clauses need three (`m`, the rank `k`, the number of
  attempts). Input: `M` row-major then `y`; index registers hold the parameters (`[n, m]` in the
  first clause, `par …` in the others). Programs and `par` are chosen before `n` and the oracle.
* *The query bound `m`.* One function `m = mf n ε` (the paper sets it from `n`, `q`, `ε` in the
  proof), shared by all four clauses, with `m ≤ C(ε⁻² log(n/ε) + 1)` always and
  `m ≤ C(γ⁻¹ log(n/γ) + 1)` when `q ≥ 200/γ`. The `+ 1` only matters for `n ≤ 2` (for `n ≥ 3`,
  `ε < 1` and `γ ≤ 1` give `log(n/ε), log(n/γ) > 1`); it is needed because `m ≥ 1` while
  `ε⁻² log(n/ε)` can be below `1` at `n = 1`.
* *Constants.* In the first two clauses one absolute constant `C`, chosen before the field. In the
  clauses with `ω` and `o(1)` the constant `C'` comes after the field and the slack `ε' > 0`, as in
  the published `LinSysAmp.proposition_4_8`; `ω = omegaAlg F`.
* *Time.* Calls and field operations are bounded separately on every run, for every oracle and
  every input with `M` invertible: clause 1, `calls ≤ m`, `ops ≤ C n² m`; clause 2, both multiplied
  by `C log(1/(βδ))`; clause 3, `calls ≤ C' m log(1/δ)` and
  `ops ≤ C'(n² m + n² k^{ω−2+ε'}) log(1/δ)`; clause 4, the same with `n^{2+ε'}` for
  `n² k^{ω−2+ε'}` at `k = ⌈n^{0.32}⌉`.
* *Never wrong* (clause 1): every halted run with an output outputs `M⁻¹y`. The later clauses do not
  print it and do not state it.
* *Success.* Hypothesis (7) is `1/q + ε ≤ lineqAgreement O`. Clause 1: for every function
  `y : GL_n(F) → Fⁿ`, `E_{M ← GL_n}[Pr[output = M⁻¹y(M)]] ≥ 7/8`. Clauses 2–4: the normalized count
  of `M ∈ GL_n(F)` on which every right-hand side succeeds with probability `≥ 1 − δ` is at least
  `1 − β`, resp. `1 − 74 q^{−2k}`.
* `q = Fintype.card F`, `n ≥ 1` (display (7) divides by `n`), `log` natural. -/
theorem theorem_6_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∃ mf : ℕ → ℝ → ℕ,
        (∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε →
          ((mf n ε : ℝ) ≤ C * (1 / ε ^ 2 * Real.log (n / ε) + 1)) ∧
          (200 / (1 / (Fintype.card F : ℝ) + ε) ≤ (Fintype.card F : ℝ) →
            (mf n ε : ℝ) ≤ C * (1 / (1 / (Fintype.card F : ℝ) + ε) *
              Real.log (n / (1 / (Fintype.card F : ℝ) + ε)) + 1))) ∧
        (∃ P : OProgram F,
          ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∀ O : LinSysAmp.Oracle n F,
            let m : ℕ := mf n ε
            let Bo : ℝ := C * (n : ℝ) ^ 2 * m
            let N : ℕ := stepBudget m Bo
            (∀ (M : LinSysAmp.InvMat n F) (y : Fin n → F),
              OHaltsWithin (lineqIface O) P (oinit [(n : ℤ), (m : ℤ)] (flatMat M.1 ++ List.ofFn y))
                N m Bo) ∧
            (∀ (M : LinSysAmp.InvMat n F) (y : Fin n → F),
              ∀ σ ∈ (orun (lineqIface O) P N
                  (oinit [(n : ℤ), (m : ℤ)] (flatMat M.1 ++ List.ofFn y))).support,
                ∀ o : Out F, σ.status = .done (some o) → o = .vec (List.ofFn (M.1⁻¹ *ᵥ y))) ∧
            (1 / (Fintype.card F : ℝ) + ε ≤ lineqAgreement O →
              ∀ y : LinSysAmp.InvMat n F → (Fin n → F),
                7 / 8 ≤ (Fintype.card (LinSysAmp.InvMat n F) : ℝ)⁻¹ *
                  ∑ M : LinSysAmp.InvMat n F,
                    oOutputProb (lineqIface O) P
                      (oinit [(n : ℤ), (m : ℤ)] (flatMat M.1 ++ List.ofFn (y M))) N
                      (.vec (List.ofFn (M.1⁻¹ *ᵥ y M))))) ∧
        (∃ P : OProgram F, ∃ par : ℕ → ℝ → ℝ → ℝ → List ℤ,
          ∀ n : ℕ, 1 ≤ n → ∀ ε β δ : ℝ, 0 < ε → 0 < β → β < 1 / 2 → 0 < δ → δ < 1 / 2 →
          ∀ O : LinSysAmp.Oracle n F,
            let m : ℕ := mf n ε
            let Bc : ℝ := C * m * Real.log (1 / (β * δ))
            let Bo : ℝ := C * (n : ℝ) ^ 2 * m * Real.log (1 / (β * δ))
            let N : ℕ := stepBudget Bc Bo
            (∀ (M : LinSysAmp.InvMat n F) (y : Fin n → F),
              OHaltsWithin (lineqIface O) P (oinit (par n ε β δ) (flatMat M.1 ++ List.ofFn y))
                N Bc Bo) ∧
            (1 / (Fintype.card F : ℝ) + ε ≤ lineqAgreement O →
              1 - β ≤ ((Finset.univ.filter fun M : LinSysAmp.InvMat n F => ∀ y : Fin n → F,
                  1 - δ ≤ oOutputProb (lineqIface O) P
                    (oinit (par n ε β δ) (flatMat M.1 ++ List.ofFn y)) N
                    (.vec (List.ofFn (M.1⁻¹ *ᵥ y)))).card : ℝ) /
                (Fintype.card (LinSysAmp.InvMat n F) : ℝ))) ∧
        (∀ ε' : ℝ, 0 < ε' → ∃ P : OProgram F, ∃ par : ℕ → ℕ → ℝ → ℝ → List ℤ, ∃ C' : ℝ, 0 < C' ∧
          ∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 / 2 →
          ∀ O : LinSysAmp.Oracle n F,
            let m : ℕ := mf n ε
            let Bc : ℝ := C' * m * Real.log (1 / δ)
            let Bo : ℝ := C' * ((n : ℝ) ^ 2 * m +
              (n : ℝ) ^ 2 * (k : ℝ) ^ (LinSysAmp.omegaAlg F - 2 + ε')) * Real.log (1 / δ)
            let N : ℕ := stepBudget Bc Bo
            (∀ (M : LinSysAmp.InvMat n F) (y : Fin n → F),
              OHaltsWithin (lineqIface O) P (oinit (par n k ε δ) (flatMat M.1 ++ List.ofFn y))
                N Bc Bo) ∧
            (1 / (Fintype.card F : ℝ) + ε ≤ lineqAgreement O →
              1 - 74 / (Fintype.card F : ℝ) ^ (2 * k) ≤
                ((Finset.univ.filter fun M : LinSysAmp.InvMat n F => ∀ y : Fin n → F,
                  1 - δ ≤ oOutputProb (lineqIface O) P
                    (oinit (par n k ε δ) (flatMat M.1 ++ List.ofFn y)) N
                    (.vec (List.ofFn (M.1⁻¹ *ᵥ y)))).card : ℝ) /
                (Fintype.card (LinSysAmp.InvMat n F) : ℝ))) ∧
        (∀ ε' : ℝ, 0 < ε' → ∃ P : OProgram F, ∃ par : ℕ → ℝ → ℝ → List ℤ, ∃ C' : ℝ, 0 < C' ∧
          ∀ n : ℕ, 1 ≤ n → ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 / 2 →
          ∀ O : LinSysAmp.Oracle n F,
            let k : ℕ := ⌈(n : ℝ) ^ (0.32 : ℝ)⌉₊
            let m : ℕ := mf n ε
            let Bc : ℝ := C' * m * Real.log (1 / δ)
            let Bo : ℝ := C' * ((n : ℝ) ^ 2 * m + (n : ℝ) ^ (2 + ε')) * Real.log (1 / δ)
            let N : ℕ := stepBudget Bc Bo
            (∀ (M : LinSysAmp.InvMat n F) (y : Fin n → F),
              OHaltsWithin (lineqIface O) P (oinit (par n ε δ) (flatMat M.1 ++ List.ofFn y))
                N Bc Bo) ∧
            (1 / (Fintype.card F : ℝ) + ε ≤ lineqAgreement O →
              1 - 74 / (Fintype.card F : ℝ) ^ (2 * k) ≤
                ((Finset.univ.filter fun M : LinSysAmp.InvMat n F => ∀ y : Fin n → F,
                  1 - δ ≤ oOutputProb (lineqIface O) P
                    (oinit (par n ε δ) (flatMat M.1 ++ List.ofFn y)) N
                    (.vec (List.ofFn (M.1⁻¹ *ᵥ y)))).card : ℝ) /
                (Fintype.card (LinSysAmp.InvMat n F) : ℝ))) := by sorry

end LinSysAmp.Supplement
