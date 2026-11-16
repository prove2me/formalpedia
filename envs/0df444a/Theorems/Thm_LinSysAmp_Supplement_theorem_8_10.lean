-- Prove2me | Theorems.Thm_LinSysAmp_Supplement_theorem_8_10
-- name    : LinSysAmp.Supplement.theorem_8_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:54:42.14521+00:00
-- url     : https://prove2.me/theorems/a42305ee-7efe-4741-af6b-34a801b28a5a
-- title:
--   Theorem 8.10 — rank computation from key recovery
-- statement:
--   Let $N\ge1$, $0<\alpha,\delta<1/2$, and $\mathbb F_q$ a finite field. For every $1\le c\le N$ let $P_c$ be an algorithm, taking time $T$ per call, which recovers the key with probability at least $\alpha$ on the ideal distribution of the protocol of dimension $c$ over $\mathbb F_q$. Let
--   $$\ell_N=\lceil\log_2(N+1)\rceil,\qquad L=1+\Big\lceil\frac8\alpha\log64\Big\rceil,\qquad w=\Big\lceil\log_4\frac{4\ell_N}{\delta}\Big\rceil.$$
--   If $q\ge\max\{128L,16\ell_N/\delta\}$, there is an algorithm which, given a uniformly random matrix $A\in\mathbb F_q^{N\times N}$ of rank $\rho$, outputs $\rho$ with probability at least $1-\delta$, for every $\rho\in\{0,\dots,N\}$. It makes at most $\ell_N Lw$ calls to the algorithms $P_c$ and runs in time
--   $$O(\ell_NLw(T+N^2))=O\Big(\frac{T+N^2}{\alpha}\log(N+1)\log\frac{\log(N+1)}{\delta}\Big).$$
--
--   This reduces computing the rank of random matrices (for every rank distribution) to breaking the key-agreement protocol, which gives the protocol's security from the average-case hardness of rank computation.
--
--   **Formalization Note** The algorithm is a program of the oracle machine whose mode-$c$ calls go to $P_c$; it outputs the integer $\rho$. Both printed forms of the time bound are stated, with one absolute constant. $\log$ is natural, $\log_2,\log_4$ are `Real.logb 2`, `Real.logb 4`.
--
--   Differences from the source:
--   - encoding: runs in time O(ℓ_N L w (T + N²)) = O((T + N²)/α · log(N + 1) · log(log(N + 1)/δ)) → on every run: calls ≤ ℓ_N L w, operations ≤ C·ℓ_N L w·N² and operations ≤ C·N²·α⁻¹·log(N + 1)·log(log(N + 1)/δ); reason: T is charged per call; both printed forms are stated
--   - reading: an O(·) bound with an unnamed constant and "there is an algorithm" → one absolute constant C, chosen before the field, and one program per field chosen before n, the parameters and the oracle; reason: the proof's constants are absolute and the reduction is black-box and uniform; this is the standard reading of O(·)
--   - encoding: "a uniformly random matrix of rank ρ" → the average over the N × N matrices of rank exactly ρ of the probability of outputting ρ; reason: uniform distribution on a finite set
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Theorem 8.10, p.51 (PDF p.53)

import Mathlib
import Definitions.Def_LinSysAmp_lineqSuccess
import Definitions.Def_LinSysAmp_Supplement_OracleMachine
import Definitions.Def_LinSysAmp_Supplement_KeyAgreement

set_option autoImplicit false

open Matrix

namespace LinSysAmp.Supplement

universe u

/-- Theorem 8.10 (Rank computation from key recovery), p.51 (PDF p.53). Couteau, Melissaris,
Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography*,
arXiv:2611.04680 (version held, sha256 af7a90ac…).

"Let N ≥ 1 and 0 < α, δ < 1/2. For every 1 ≤ c ≤ N, let P_c be a time-T algorithm which recovers
the key with probability at least α, on the ideal distribution of the protocol of dimension c over
F_q. Let ℓ_N = ⌈log₂(N + 1)⌉, L = 1 + ⌈(8/α) log 64⌉, w = ⌈log₄(4ℓ_N/δ)⌉. If
q ≥ max{128L, 16ℓ_N/δ}, there is an algorithm which, given a uniformly random matrix A ∈ F_q^{N×N}
of rank ρ, outputs ρ with probability at least 1 − δ, for every ρ ∈ {0, …, N}. It makes at most
ℓ_N·L·w calls to the algorithms P_c, and runs in time
O(ℓ_N L w (T + N²)) = O((T + N²)/α · log(N + 1) · log(log(N + 1)/δ))."

**Formalization Note.**
* *Oracles.* `P c` is a key-recovery algorithm of dimension `c` for every `c`; only those with
  `1 ≤ c ≤ N` are assumed to succeed: `α ≤ keySuccess (P c)` on the ideal distribution
  (`M ← GL_c(F)`, `r, y ← F^c`, `K = rM⁻¹y`). Nothing is assumed about `c = 0` or `c > N`.
* *Algorithm.* A program of `LinSysAmp.Supplement.OracleMachine` with the interface `keyIface P`: a
  call in mode `c` passes a dimension-`c` transcript to `P c`. Input `A` row-major; index registers
  `par N α δ`; the output is the integer `ρ` (`haltInt`). Program and `par` are chosen for the field
  only, before `N`, `α`, `δ` and the oracles.
* *Calls and time.* On every run and every input `A`: at most `ℓ_N L w` calls in total (to any of
  the `P c`), and at most `C ℓ_N L w N²` field operations, and also at most
  `C N²/α · log(N + 1) · log(log(N + 1)/δ)` (the printed right-hand form); `C` is absolute, chosen
  before the field.
* *Success.* For every `ρ ≤ N`, the average over the `N × N` matrices of rank exactly `ρ`
  (`rankAvg`) of the probability that the output is `ρ` is at least `1 − δ`.
* `log₂`, `log₄` are `Real.logb 2`, `Real.logb 4`; `log` is natural; `q = Fintype.card F`. The
  sentence after the theorem ("The condition on the field size is q ≥ C max{…}") is a remark, not
  part of the statement. -/
theorem theorem_8_10 :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∃ P : OProgram F, ∃ par : ℕ → ℝ → ℝ → List ℤ,
        ∀ N : ℕ, 1 ≤ N → ∀ α δ : ℝ, 0 < α → α < 1 / 2 → 0 < δ → δ < 1 / 2 →
        ∀ Pc : (c : ℕ) → KeyRec c F,
          let ℓN : ℕ := ⌈Real.logb 2 ((N : ℝ) + 1)⌉₊
          let L : ℕ := 1 + ⌈8 / α * Real.log 64⌉₊
          let w : ℕ := ⌈Real.logb 4 (4 * (ℓN : ℝ) / δ)⌉₊
          let Bc : ℝ := (ℓN : ℝ) * L * w
          let Bo : ℝ := C * ((ℓN : ℝ) * L * w) * (N : ℝ) ^ 2
          let Nst : ℕ := stepBudget Bc Bo
          (∀ c : ℕ, 1 ≤ c → c ≤ N → α ≤ keySuccess (Pc c)) →
          max (128 * (L : ℝ)) (16 * (ℓN : ℝ) / δ) ≤ (Fintype.card F : ℝ) →
          (∀ A : Matrix (Fin N) (Fin N) F,
            OHaltsWithin (keyIface Pc) P (oinit (par N α δ) (flatMat A)) Nst Bc Bo ∧
            ∀ σ ∈ (orun (keyIface Pc) P Nst (oinit (par N α δ) (flatMat A))).support,
              (σ.ops : ℝ) ≤ C * (N : ℝ) ^ 2 / α * Real.log ((N : ℝ) + 1) *
                Real.log (Real.log ((N : ℝ) + 1) / δ)) ∧
          (∀ ρ : ℕ, ρ ≤ N →
            1 - δ ≤ rankAvg N ρ fun A =>
              oOutputProb (keyIface Pc) P (oinit (par N α δ) (flatMat A)) Nst (.int (ρ : ℤ))) := by sorry

end LinSysAmp.Supplement
