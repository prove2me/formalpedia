-- Prove2me | Theorems.Thm_LinSysAmp_Supplement_theorem_5_5
-- name    : LinSysAmp.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:50:59.081934+00:00
-- url     : https://prove2.me/theorems/c1389a61-87fa-4ee1-83e7-ab5a068e42db
-- title:
--   Theorem 5.5 — worst-case OMv from an average-case data structure
-- statement:
--   Let $\mathbb F_q$ be a finite field and $n\ge1$. Let $D$ be a data structure for OMv (Definition 5.3) with preprocessing time $P$ and query time $T$, which solves OMv with probability $\alpha$:
--   $$\Pr_{A\leftarrow\mathbb F_q^{n\times n},\,v\leftarrow\mathbb F_q^n,\,D}[D(A;v)=Av]\ge\alpha,$$
--   and let $0<\delta<1/2$. Then there is a data structure $E_{\mathrm{wc}}$ with preprocessing time $O((P+n^2)\alpha^{-1}\log(1/\delta))$ and query time $O((T+n)\alpha^{-1}\log(1/\delta))$ such that
--   $$\Pr[E_{\mathrm{wc}}(A;v)=Av]\ge1-\delta\quad\text{for all }A\in\mathbb F_q^{n\times n},\ v\in\mathbb F_q^n,$$
--   the probability being over the coins of preprocessing and of the query.
--
--   The theorem shows that the OMv conjecture over finite fields is equivalent to its average-case version with any constant success probability.
--
--   **Formalization Note** $E_{\mathrm{wc}}$ is a pair of oracle-machine programs; mode $0$ calls $D_{\mathrm{pre}}$ and mode $1$ calls $D_{\mathrm{query}}$ on a stored state. The guarantee is for a single query, as Definition 5.3 states.
--
--   Differences from the source:
--   - encoding: preprocessing time O((P + n²)α⁻¹ log(1/δ)) and query time O((T + n)α⁻¹ log(1/δ)) → preprocessing: at most C·α⁻¹·log(1/δ) calls, none to D_query, and C·n²·α⁻¹·log(1/δ) operations; each query (from every reachable preprocessing state): at most C·α⁻¹·log(1/δ) calls, none to D_pre, and C·n·α⁻¹·log(1/δ) operations; reason: D_pre costs P and D_query costs T per call, so these bounds give the printed times
--   - reading: an O(·) bound with an unnamed constant and "there is an algorithm" → one absolute constant C, chosen before the field, and one program per field chosen before n, the parameters and the oracle; reason: the proof's constants are absolute and the reduction is black-box and uniform; this is the standard reading of O(·)
--   - generalization: the cost (and correctness) guarantees are stated for an oracle with the assumed success probability α → they hold for every oracle; only the success guarantee assumes the success probability α; reason: the reduction's cost never depends on the oracle's quality; the source's instance is the special case
--   - encoding: α unconstrained above → α ≤ 1 added; reason: the hypothesis α ≤ Pr[D(A;v) = Av] already forces it; without it the unconditional cost bounds could not be met for large α
--   - encoding: n is an integer dimension → 1 ≤ n; reason: §3.1 fixes n ≥ 1 ("For an integer n ≥ 1")
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Theorem 5.5, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_LinSysAmp_Supplement_OracleMachine
import Definitions.Def_LinSysAmp_Supplement_OMv

set_option autoImplicit false

open Matrix

namespace LinSysAmp.Supplement

universe u v

/-- Theorem 5.5 (Worst-case to average-case reduction for OMv), p.29 (PDF p.31). Couteau,
Melissaris, Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and Fine-Grained
Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…).

"Let D be a data structure with preprocessing time P and query time T, which solves OMv with
probability α, and let 0 < δ < 1/2. Then there is a data structure E_wc with preprocessing time
O((P + n²)α⁻¹ log(1/δ)) and query time O((T + n)α⁻¹ log(1/δ)), such that Pr[E_wc(A; v) = Av] ≥ 1 − δ
for all A ∈ F_q^{n×n} and v ∈ F_qⁿ."

**Formalization Note.**
* *Data structures.* `D` is an `OMvDS n F S` over an arbitrary state type `S` (Definition 5.3).
  `E_wc` is a pair of programs `(P_pre, P_query)` of the machine `LinSysAmp.Supplement.OracleMachine`
  with the interface `omvIface D` (mode `0` = `D_pre`, mode `1` = `D_query`). Preprocessing runs
  `P_pre` on `A` (row-major, index registers `par n α δ`); a query runs `P_query` from the final
  preprocessing configuration with `v` added (`queryInit`). The programs and `par` are chosen for
  the field only, before `n`, `α`, `δ`, `S` and `D` (α is known, p.23).
* *Time.* On every preprocessing run: at most `C α⁻¹ log(1/δ)` oracle calls, all of them to `D_pre`
  (no `D_query` call), and `C n² α⁻¹ log(1/δ)` field operations, i.e. preprocessing time
  `O((P + n²)α⁻¹ log(1/δ))`. On every query run from every reachable preprocessing state: at most
  `C α⁻¹ log(1/δ)` calls, none to `D_pre`, and `C n α⁻¹ log(1/δ)` field operations, i.e. query time
  `O((T + n)α⁻¹ log(1/δ))`. One absolute constant `C`, chosen before the field.
* *Success.* "Solves OMv with probability α" is `α ≤ omvSuccess D` (`A ← F^{n×n}`, `v ← Fⁿ`).
  The guarantee is for a single query, as Definition 5.3 states: for all `A` and `v`, over the
  coins of preprocessing and query, the query outputs `Av` with probability at least `1 − δ`.
* `n ≥ 1` (§3.1).
* `α ≤ 1` is added: the hypothesis `α ≤ omvSuccess D` already forces it; the cost clauses hold
  for every data structure, and without it the bounds could fall below one step. -/
theorem theorem_5_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∃ Ppre Pq : OProgram F, ∃ par : ℕ → ℝ → ℝ → List ℤ,
        ∀ n : ℕ, 1 ≤ n → ∀ α δ : ℝ, 0 < α → α ≤ 1 → 0 < δ → δ < 1 / 2 →
        ∀ (S : Type v) (D : OMvDS n F S),
          let Bc : ℝ := C / α * Real.log (1 / δ)
          let Bpre : ℝ := C * (n : ℝ) ^ 2 / α * Real.log (1 / δ)
          let Bq : ℝ := C * (n : ℝ) / α * Real.log (1 / δ)
          let N₁ : ℕ := stepBudget Bc Bpre
          let N₂ : ℕ := stepBudget Bc Bq
          (∀ A : Matrix (Fin n) (Fin n) F,
            OHaltsWithin (omvIface D) Ppre (oinit (par n α δ) (flatMat A)) N₁ Bc Bpre ∧
            ∀ σ ∈ (orun (omvIface D) Ppre N₁ (oinit (par n α δ) (flatMat A))).support,
              σ.callsAt 1 = 0) ∧
          (∀ A : Matrix (Fin n) (Fin n) F,
            ∀ σ ∈ (orun (omvIface D) Ppre N₁ (oinit (par n α δ) (flatMat A))).support,
            ∀ v : Fin n → F,
              OHaltsWithin (omvIface D) Pq (queryInit σ v) N₂ Bc Bq ∧
              ∀ σ' ∈ (orun (omvIface D) Pq N₂ (queryInit σ v)).support, σ'.callsAt 0 = 0) ∧
          (α ≤ omvSuccess D → ∀ (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F),
            1 - δ ≤ ewcAnswerProb D Ppre Pq (par n α δ) N₁ N₂ A v (A *ᵥ v)) := by sorry

end LinSysAmp.Supplement
