-- Prove2me | Theorems.Thm_LinSysAmp_Supplement_theorem_6_5
-- name    : LinSysAmp.Supplement.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:53:30.247897+00:00
-- url     : https://prove2.me/theorems/4b1c96d8-8c80-4642-86d1-c063e658bae1
-- title:
--   Theorem 6.5 — worst-case OMv from data structures with expected agreement $1/q+\varepsilon$
-- statement:
--   Let $\mathbb F_q$ be a finite field and $n\ge1$. Let $D$ be a data structure for OMv (Definition 5.3) with preprocessing time $P$ and query time $T$ and expected agreement $1/q+\varepsilon$ for some $\varepsilon>0$:
--   $$\mathbb E_{A\leftarrow\mathbb F_q^{n\times n},\,v\leftarrow\mathbb F_q^n,\,D}[\mathrm{agr}(D(A;v),Av)]\ge\frac1q+\varepsilon.$$
--   For every $0<\delta<1/2$ there is a data structure $E_{\mathrm{wc}}$ with preprocessing time $O((P+n^2)\varepsilon^{-2}\log(nq)\log(1/\delta))$ and query time $O((T+n\log t)\varepsilon^{-2}\log(nq)\log(1/\delta))$, where $t=\lceil6\varepsilon^{-2}\log(100nq)\rceil$, such that
--   $$\Pr[E_{\mathrm{wc}}(A;v)=Av]\ge1-\delta\quad\text{for all }A\in\mathbb F_q^{n\times n},\ v\in\mathbb F_q^n.$$
--
--   This extends Theorem 5.5 to data structures that are only slightly better than random on each coordinate.
--
--   **Formalization Note** As in Theorem 5.5: $E_{\mathrm{wc}}$ is a pair of oracle-machine programs, the guarantee is for a single query, and preprocessing and query costs are counted separately.
--
--   Differences from the source:
--   - encoding: preprocessing time O((P + n²)ε⁻² log(nq) log(1/δ)) and query time O((T + n log t)ε⁻² log(nq) log(1/δ)) → preprocessing: at most C·ε⁻²·log(nq)·log(1/δ) calls, none to D_query, and C·n²·ε⁻²·log(nq)·log(1/δ) operations; each query: at most C·ε⁻²·log(nq)·log(1/δ) calls, none to D_pre, and C·n·log t·ε⁻²·log(nq)·log(1/δ) operations; reason: D_pre costs P and D_query costs T per call, so these bounds give the printed times
--   - reading: an O(·) bound with an unnamed constant and "there is an algorithm" → one absolute constant C, chosen before the field, and one program per field chosen before n, the parameters and the oracle; reason: the proof's constants are absolute and the reduction is black-box and uniform; this is the standard reading of O(·)
--   - generalization: the cost (and correctness) guarantees are stated for an oracle with the assumed expected agreement 1/q + ε → they hold for every oracle; only the success guarantee assumes the expected agreement 1/q + ε; reason: the reduction's cost never depends on the oracle's quality; the source's instance is the special case
--   - encoding: ε unconstrained above → ε ≤ 1 added; reason: the hypothesis 1/q + ε ≤ expected agreement ≤ 1 already forces it; without it the unconditional cost bounds could not be met for large ε
--   - encoding: n is an integer dimension → 1 ≤ n; reason: §3.1 fixes n ≥ 1 ("For an integer n ≥ 1")
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Theorem 6.5, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_LinSysAmp_Supplement_OracleMachine
import Definitions.Def_LinSysAmp_Supplement_OMv

set_option autoImplicit false

open Matrix

namespace LinSysAmp.Supplement

universe u v

/-- Theorem 6.5 (Worst-case OMv from approximate data structures), p.40 (PDF p.42). Couteau,
Melissaris, Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and Fine-Grained
Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…).

"Let D be a data structure with preprocessing time P and query time T, which has expected agreement
1/q + ε, for some ε > 0. For every 0 < δ < 1/2, there is a data structure E_wc with preprocessing
time O((P + n²)ε⁻² log(nq) log(1/δ)) and query time O((T + n log t)ε⁻² log(nq) log(1/δ)), where
t = ⌈6ε⁻² log(100nq)⌉, such that Pr[E_wc(A; v) = Av] ≥ 1 − δ for all A ∈ F_q^{n×n} and v ∈ F_qⁿ."

**Formalization Note.**
* *Data structures* as in `theorem_5_5`: `D : OMvDS n F S` over an arbitrary state type, `E_wc` a
  pair of programs of `LinSysAmp.Supplement.OracleMachine` with the interface `omvIface D`, query
  started from the final preprocessing configuration (`queryInit`); programs and `par` chosen for
  the field only, before `n`, `ε`, `δ`, `S` and `D` (ε is known, p.36).
* *Time.* Preprocessing: at most `C ε⁻² log(nq) log(1/δ)` calls, none to `D_query`, and
  `C n² ε⁻² log(nq) log(1/δ)` field operations. Query (from every reachable preprocessing state): at
  most `C ε⁻² log(nq) log(1/δ)` calls, none to `D_pre`, and `C n log t · ε⁻² log(nq) log(1/δ)` field
  operations, `t = ⌈6ε⁻² log(100nq)⌉`. One absolute constant `C`, chosen before the field.
* *Expected agreement* `1/q + ε` is `1/q + ε ≤ omvAgreement D` (Definition 5.3).
* *Success.* Single query: for all `A`, `v`, `Pr[E_wc(A; v) = Av] ≥ 1 − δ`.
* `q = Fintype.card F`, `n ≥ 1` (§3.1).
* `ε ≤ 1` is added: the hypothesis `1/q + ε ≤ omvAgreement D ≤ 1` already forces it; the cost
  clauses hold for every data structure, and without it `ε⁻²` could be made arbitrarily small. -/
theorem theorem_6_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∃ Ppre Pq : OProgram F, ∃ par : ℕ → ℝ → ℝ → List ℤ,
        ∀ n : ℕ, 1 ≤ n → ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 / 2 →
        ∀ (S : Type v) (D : OMvDS n F S),
          let q : ℝ := Fintype.card F
          let t : ℕ := ⌈6 / ε ^ 2 * Real.log (100 * (n : ℝ) * q)⌉₊
          let Bc : ℝ := C / ε ^ 2 * Real.log (n * q) * Real.log (1 / δ)
          let Bpre : ℝ := C * (n : ℝ) ^ 2 / ε ^ 2 * Real.log (n * q) * Real.log (1 / δ)
          let Bq : ℝ := C * (n : ℝ) * Real.log t / ε ^ 2 * Real.log (n * q) * Real.log (1 / δ)
          let N₁ : ℕ := stepBudget Bc Bpre
          let N₂ : ℕ := stepBudget Bc Bq
          (∀ A : Matrix (Fin n) (Fin n) F,
            OHaltsWithin (omvIface D) Ppre (oinit (par n ε δ) (flatMat A)) N₁ Bc Bpre ∧
            ∀ σ ∈ (orun (omvIface D) Ppre N₁ (oinit (par n ε δ) (flatMat A))).support,
              σ.callsAt 1 = 0) ∧
          (∀ A : Matrix (Fin n) (Fin n) F,
            ∀ σ ∈ (orun (omvIface D) Ppre N₁ (oinit (par n ε δ) (flatMat A))).support,
            ∀ v : Fin n → F,
              OHaltsWithin (omvIface D) Pq (queryInit σ v) N₂ Bc Bq ∧
              ∀ σ' ∈ (orun (omvIface D) Pq N₂ (queryInit σ v)).support, σ'.callsAt 0 = 0) ∧
          (1 / q + ε ≤ omvAgreement D → ∀ (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F),
            1 - δ ≤ ewcAnswerProb D Ppre Pq (par n ε δ) N₁ N₂ A v (A *ᵥ v)) := by sorry

end LinSysAmp.Supplement
