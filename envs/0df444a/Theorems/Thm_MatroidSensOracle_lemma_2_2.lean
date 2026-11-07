-- Prove2me | Theorems.Thm_MatroidSensOracle_lemma_2_2
-- name    : MatroidSensOracle.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:48:48.887419+00:00
-- url     : https://prove2.me/theorems/d57100d2-180b-4b7f-83ce-9fdfa145234a
-- title:
--   Lemma 2.2: $\det(M)$ of $M\in\mathbb F_d[Y]^{N\times N}$ in $\widetilde O(dN^\omega)$ field operations (deterministic, worst case)
-- statement:
--   Let $\mathbb F$ be a field and $\omega=\omega_{\mathbb F}$ the exponent of matrix multiplication over $\mathbb F$. For every $\tau>0$ there are constants $C,K,b$ and one program of the algebraic RAM over $\mathbb F$ that draws no coins such that, for every $N\ge1$, every $d$, every $N\times N$ matrix $M$ whose entries are polynomials in $Y$ of degree at most $d$, and every word width $w\ge b(\lfloor\log_2(N+d+2)\rfloor+1)$: run on the words $N,d$ and the coefficients of $M$, the program halts within
--   $$C\,(d+1)\,N^{\omega+\tau}\,\bigl(\log_2(dN+2)\bigr)^{K}$$
--   steps with the coefficients of $\det M$ (of degrees $0,\dots,Nd$) in field cells $0,\dots,Nd$.
--
--   It is the primitive behind the weighted oracles of §3.
--
--   Differences from the source:
--   - reading: one can compute det(M) in Õ(dN^ω) field operations (machine and determinism not stated) → a coin-free program of the algebraic RAM over F, worst-case steps counting every instruction; reason: the strongest reading; field operations are at most the steps, and deterministic algorithms of this cost are known (Labahn–Neiger–Zhou 2017); expected time is not allowed
--   - encoding: O(N^ω) → C N^{ω+τ} for every τ > 0, ω = omega F; reason: ω is an infimum over admissible exponents
--   - encoding: Õ(d N^ω), N × N matrices → C (d+1) N^{ω+τ} (log₂(dN+2))^K for N ≥ 1; reason: d + 1 gives constant matrices (d = 0) the bound N^ω; the same bound as Õ(dN^ω) for d ≥ 1
--   - encoding: compute det(M) → words N, d and the coefficients of the entries row-major in; the coefficients of det M in field cells 0, …, Nd out; reason: input and output layout
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Lemma 2.2, p.12 (PDF p.15)

import Mathlib
import Definitions.Def_MatroidSensOracle_AlgRAM
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

open Polynomial

namespace MatroidSensOracle

/-- **Lemma 2.2.** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256 0de50841…), p.12
(PDF p.15): "For any matrix M ∈ F_d[Y]^{N×N}, one can compute det(M) in Õ(dN^ω) field operations."
(F_d[Y]: polynomials in Y over F of degree at most d.)

**Formalization Note.**
* **Machine:** the algebraic RAM over `F` (`MatroidSensOracle.aexec`); time counts every
  instruction (field and word operations). The program draws no coins and the bound is worst case:
  the deterministic reading (the lemma says neither deterministic nor randomized; expected time is
  not allowed).
* **ω** is `omega F` (the published `OAI.MatrixMultiplication.Arithmetic.omega`), the exponent of
  matrix multiplication over `F`; `O(N^ω)` is read as `C N^{ω+τ}` for every `τ > 0`, because `ω` is an
  infimum.
* **Õ** hides `(log₂(dN + 2))^K`. `d` is replaced by `d + 1` so that constant matrices (`d = 0`)
  get the bound `N^ω`.
* **Input/output:** words `N, d`; field cells: the `d + 1` coefficients of each entry, row-major
  (`polyMatrixFields`). On halting, field cell `j` holds the coefficient of `Y^j` in `det M`, for
  `j = 0, …, Nd`. The program works for every word width `w ≥ b(⌊log₂(N + d + 2)⌋ + 1)`. `N ≥ 1`. -/
theorem lemma_2_2 (F : Type) [Field F] [DecidableEq F] :
    ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (P : List AInstr), (∀ i ∈ P, ¬ i.IsCoin) ∧
      ∀ (N d : ℕ) (M : Matrix (Fin N) (Fin N) F[X]), 1 ≤ N → (∀ i j, (M i j).natDegree ≤ d) →
        ∀ w : ℕ, b * (Nat.log 2 (N + d + 2) + 1) ≤ w →
          ∃ st, aexec P (fun _ => 0)
              ⌊C * ((d : ℝ) + 1) * (N : ℝ) ^ (OAI.MatrixMultiplication.Arithmetic.omega F + τ) *
                (Real.logb 2 ((d : ℝ) * N + 2)) ^ K⌋₊ 0 0
              (aloadWords w [(N : ℤ), d]) (aloadFields (polyMatrixFields d M)) = some st ∧
            ∀ j : ℕ, j ≤ N * d → st.2 j = (M.det).coeff j := by sorry

end MatroidSensOracle
