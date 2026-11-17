-- Prove2me | Theorems.Thm_LinfContractionFP_Supplement_theorem_2
-- name    : LinfContractionFP.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:52:23.824493+00:00
-- url     : https://prove2.me/theorems/f85637a8-9a72-4575-9eba-b043f57d6700
-- title:
--   Theorem 2 — $\mathrm{Amplify}(0,2\kappa,0,n,n)$ solves the extremal amplification game with $(\log(\kappa/\rho))^{C\log n}$ Oracle calls
-- statement:
--   This is the main result on the **extremal amplification game** (Problem 1). An adversarial Oracle holds a secret vector $\sigma \in \mathbb R^n$. Given a shift vector $b \in \mathbb R^n$, the Oracle either declares defeat or returns a labeling $\ell \in \{-1,+1\}^n$ that tags with $-1$ every coordinate $i$ with $\sigma_i + b_i$ within $\rho$ of $\min(\sigma+b)$, and with $+1$ every coordinate within $\rho$ of $\max(\sigma+b)$. A labeling $\ell$ is **$\kappa$-accurate** for $\sigma$ if it tags with $-1$ every coordinate within $\kappa$ of $\min\sigma$ and with $+1$ every coordinate within $\kappa$ of $\max\sigma$.
--
--   **Theorem.** There are universal constants $C$ and $C'$ such that the following holds. Let $n \ge 2$ and $\kappa \ge 4\rho > 0$, let $\sigma \in \mathbb R^n$ be any secret and let the Oracle be any Oracle of accuracy $\rho$ for $\sigma$. Then the deterministic procedure $\mathrm{Amplify}(0, 2\kappa, 0, n, n)$ (Algorithm 3, started with zero shift, margin $2\kappa$, zero votes and budgets $B_+ = B_- = n$) returns either
--
--   1. an admission of defeat from the Oracle, or
--   2. a $\kappa$-accurate labeling of $\sigma$,
--
--   and it makes at most
--   $$
--   Q := \bigl(\log(\kappa/\rho)\bigr)^{C\log n}
--   $$
--   calls to the Oracle and at most $C' \cdot n \cdot Q$ arithmetic operations.
--
--   In the paper this theorem turns the thin labeler of Section 5, whose accuracy $\rho = \gamma^2\varepsilon/8$ is tiny, into a labeler of constant accuracy at a cost quasipolynomial in $\log(1/\rho)$; it is the step that makes the overall algorithm for $\ell_\infty$ contractions quasipolynomial.
--
--   **Formalization Note** The procedure is the published `amplifyRun` with its cost counters (Oracle calls and arithmetic operations, charged per line on a unit-cost real machine); $n$ is the number of coordinates and $\log$ the natural logarithm. The constants $C, C'$ are chosen before every other parameter. An admission of defeat is a payload the Oracle returned on some call; the Oracle may be adaptive (its answer may depend on the index of the call). In Lean the paper's $\kappa$ is named `k`, because `κ` names the coordinate type.
--
--   Differences from the source:
--   - generalization: "O(nQ) additional arithmetic operations" → `ops ≤ C' · n · Q` for the published per-line charge counter, which also charges control and decoding steps; reason: the counter upper-bounds the arithmetic operations in the source, so this stronger bound specializes to the printed claim.
--   - encoding: "there exists a deterministic procedure Amplify(0, 2κ, 0, n, n)" → the statement is about the specific published total function `amplifyRun O ρ 0 (2k) 0 n n`; reason: the paper names the procedure; a total function is deterministic and terminating.
--   - encoding: Oracle as a function of the call index and the shift (`IsOracle`), defeat as a payload `Sum.inl a` that the Oracle returned on some call; reason: covers every adaptive Oracle against the deterministic caller; same instances as Problem 1.
--   - encoding: coordinates indexed by `{1, …, n}` → an arbitrary finite type `κ` with `n = Fintype.card κ`; reason: finite reindexing changes no instance, and `2 ≤ card κ` is exactly `n ≥ 2`.
--   - encoding: "returns either an admission of defeat, or a κ-accurate labeling" → implications for each constructor of the sum-valued result `r.1`; reason: the two constructors are exhaustive, so the clauses are equivalent to the source's disjunction.
--   - encoding: natural-number call and operation counters compared with the real bound `Q` → order-preserving casts of both counters to `ℝ`; reason: changes no value or instance.
--   - reading: the source writes `log` without specifying a base → `Real.log`, the natural logarithm; reason: the base changes the bound only by universal constant factors absorbed into the existential exponent constant `C`, and this is the convention of the published base mission.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b4493…), Theorem 2, p.12 (Problem 1, p.11; Algorithm 3, p.15; footnote 6, p.19; proof of Theorem 2, p.20)

import Mathlib
import Definitions.Def_LinfContractionFP_IsOracle
import Definitions.Def_LinfContractionFP_amplify

namespace LinfContractionFP

namespace Supplement

/-- Theorem 2 (main result on the extremal amplification game): there are universal constants
`C` and `C'` such that, for any `n ≥ 2` coordinates and accuracies `κ ≥ 4ρ > 0` (in Lean `k` is
the paper's `κ`), any secret `σ` and any Oracle `O` of accuracy `ρ`, the deterministic procedure
`Amplify(0, 2κ, 0, n, n)` returns either an admission of defeat from Oracle or a `κ`-accurate
labeling of `σ`, using at most `Q := (log(κ/ρ))^{C log n}` calls to Oracle and at most `C'·n·Q`
arithmetic operations.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), Theorem 2, p.12: "Theorem 2. For any n ≥ 2 and κ ≥ 4ρ > 0, there
exists a deterministic procedure Amplify(0, 2κ, 0, n, n) that solves the extremal amplification
game (Problem 1) and returns either an admission of defeat from Oracle, or a κ-accurate labeling
for σ. It performs at most Q := log(κ/ρ)^{C log n} calls to Oracle and O(nQ) additional
arithmetic operations, where C is a universal constant." (Problem 1, p.11; Algorithm 3, p.15;
unit-cost real machine, footnote 6, p.19; proof in Section 6.4, p.20.)

**Formalization Note.**
* The procedure is the published `amplifyRun` (Algorithm 3 with its cost counters), called as
  `amplifyRun O ρ 0 (2 * k) 0 n n` with `n = Fintype.card κ` cast to `ℝ`: shift `0`, margin
  `2κ`, votes `0`, budgets `B₊ = B₋ = n`. It is a total function, hence deterministic and
  terminating.
* Oracle calls are `Cost.oracleCalls`, arithmetic operations `Cost.ops`, charged per line as
  listed in `amplifyAux` and `boostRound` (unit-cost real machine). The `O(nQ)` is `C' · n · Q`.
* `log` is the natural logarithm and `log(κ/ρ)^{C log n}` is `(log(κ/ρ))^{C · log n}`
  (real power), as in the proof on p.20.
* Both constants are chosen first: they do not depend on the coordinate type, the payload type,
  `σ`, `ρ`, `κ` or the Oracle.
* An "admission of defeat from Oracle" is a payload `a` that `O` returned as a defeat on some
  call. The Oracle is any `IsOracle σ ρ O`, adaptive (it may depend on the call index); labels
  `−1`/`+1` are `lo`/`hi`. -/
theorem theorem_2 : ∃ C C' : ℝ, ∀ (κ α : Type) [Fintype κ], 2 ≤ Fintype.card κ →
    ∀ (σ : κ → ℝ) (ρ k : ℝ), 0 < ρ → 4 * ρ ≤ k →
      ∀ O : ℕ → (κ → ℝ) → α ⊕ (κ → Lbl), IsOracle σ ρ O →
        let n : ℝ := Fintype.card κ
        let Q : ℝ := Real.log (k / ρ) ^ (C * Real.log n)
        let r := amplifyRun O ρ 0 (2 * k) 0 n n
        (∀ a, r.1 = Sum.inl a → ∃ t b, O t b = Sum.inl a) ∧
          (∀ ℓ, r.1 = Sum.inr ℓ → IsAccurate k σ ℓ) ∧
          (r.2.oracleCalls : ℝ) ≤ Q ∧ (r.2.ops : ℝ) ≤ C' * n * Q := by sorry

end Supplement

end LinfContractionFP
