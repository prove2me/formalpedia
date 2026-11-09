-- Prove2me | Theorems.Thm_LinfContractionFP_lemma_5
-- name    : LinfContractionFP.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:15:48.555324+00:00
-- url     : https://prove2.me/theorems/a1c19e5f-71ad-43a9-b3d0-79f1567e9589
-- title:
--   Lemma 5 — cost of amplification
-- statement:
--   There is a universal constant $C$ with the following property. Let $n\ge2$, let $O$ be any Oracle (adaptive or not, valid or not), $\rho>0$, $\tau\ge\rho$, integer votes $F\in\mathbb Z^n$ and $B_+,B_->0$ with $B_+B_-\ge1$. Put
--   $$k=1+\big\lceil\log_{4/3}(B_+B_-)\big\rceil,\qquad h=\big\lceil\log_2(\tau/\rho)\big\rceil,\qquad N=130^k\binom{h+k}{k}.$$
--   Then the call $\mathrm{Amplify}(b,\tau,F,B_+,B_-)$ makes at most $N$ boosting rounds in the whole computation, $N\le[130(h+1)]^k$, it calls Oracle at most $129N$ times, and it performs at most $C\,N\,n$ arithmetic operations.
--
--   Differences from the source:
--   - reading: O(Nn) arithmetic operations → at most C·N·n operations for a constant C chosen before n, the Oracle and all parameters; reason: the O-bound with a universal constant
--   - encoding: arithmetic operations of Algorithm 3 → the counter Cost.ops with the per-line charge schedule of amplifyAux and boostRound; reason: every line is charged at least its printed work; the schedule is in the definitions' docstrings
--   - generalization: an Oracle of the game (Problem 1) at accuracy ρ → any map O, adaptive (answers may depend on the call index) and with no validity condition on its labelings; reason: the call tree of Amplify, and so every count, does not depend on the Oracle's labels (a defeat only shortens the run); it specializes to every valid Oracle
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Lemma 5, display (15), p.20

import Mathlib
import Definitions.Def_LinfContractionFP_amplify

namespace LinfContractionFP

/-- Lemma 5 (cost of amplification): for `n ≥ 2`, Oracle accuracy `ρ > 0`, `τ ≥ ρ`, `B₊B₋ ≥ 1`,
integer votes `F` and positive `B₊, B₋`, the call `Amplify(b, τ, F, B₊, B₋)` makes at most
`N = 130^k C(h+k, k) ≤ [130(h+1)]^k` boosting rounds in the whole computation, where
`k = 1 + ⌈log_{4/3}(B₊B₋)⌉` and `h = ⌈log₂(τ/ρ)⌉`; at most `129 N` calls to Oracle; and `O(Nn)`
arithmetic operations.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), Lemma 5, p.20: "Lemma 5 (Cost of amplification). Fix n ≥ 2 and Oracle accuracy ρ > 0.
Consider the call Amplify(b, τ, F, B+, B−) with τ ≥ ρ and B+B− ≥ 1, integer votes F ∈ Z^n, and
positive potential bounds B+, B−. The total number of boosting rounds across the entire
computation is at most N := 130^k C(h+k, k) ≤ [130(h + 1)]^k, (15) where
k = 1 + ⌈log_{4/3}(B+B−)⌉ and h = ⌈log₂(τ/ρ)⌉. The number of arithmetic operations is therefore
at most O(Nn), and the number of calls to Oracle is at most 129N."

**Formalization Note.** The counters are those of `amplifyRun` (`Cost.rounds`,
`Cost.oracleCalls`, `Cost.ops`); the operation charges are listed in `amplifyAux` and
`boostRound` and never charge a line less than its printed work. The `O(Nn)` constant `C` is
universal: it is chosen before `n`, the Oracle and all the parameters. The Oracle is arbitrary,
adaptive included (the bound does not depend on its answers). -/
theorem lemma_5 : ∃ C : ℝ, ∀ (κ α : Type) [Fintype κ], 2 ≤ Fintype.card κ →
    ∀ (O : ℕ → (κ → ℝ) → α ⊕ (κ → Lbl)) (ρ : ℝ), 0 < ρ → ∀ (b : κ → ℝ) (τ : ℝ), ρ ≤ τ →
      ∀ (F : κ → ℤ) (Bp Bm : ℝ), 0 < Bp → 0 < Bm → 1 ≤ Bp * Bm →
        let k : ℕ := 1 + Nat.ceil (Real.logb (4 / 3) (Bp * Bm))
        let h : ℕ := Nat.ceil (Real.logb 2 (τ / ρ))
        let N : ℕ := 130 ^ k * (h + k).choose k
        let c := (amplifyRun O ρ b τ F Bp Bm).2
        c.rounds ≤ N ∧ N ≤ (130 * (h + 1)) ^ k ∧ c.oracleCalls ≤ 129 * N ∧
          (c.ops : ℝ) ≤ C * N * Fintype.card κ := by sorry

end LinfContractionFP
