-- Prove2me | Theorems.Thm_HypClass1_theorem_8_9
-- name    : HypClass1.theorem_8_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:39:28.284828+00:00
-- url     : https://prove2.me/theorems/c1e22a18-1b42-4efe-b333-4b64a9dba0a9
-- title:
--   Theorem 8.9 ([13], fractional Kahn–Kalai) — $p_c\le Kq_f\log\ell$ (corrected: $\ell(\mathcal B)\ge 2$)
-- statement:
--   There is a universal constant $K > 0$ such that for every finite set $X$ and every non-empty increasing family $\mathcal B \subseteq 2^X$ with $\ell(\mathcal B) \ge 2$,
--   $$
--   p_c(\mathcal B) \le K\, q_f(\mathcal B) \log \ell(\mathcal B).
--   $$
--
--   This is the fractional expectation-threshold theorem of Frankston, Kahn, Narayanan and Park, quoted by the paper. Combined with Proposition 8.10 it transfers the spread completion of Lemma 8.7 to the sparse random subgraph $H_q$ (Lemma 8.11).
--
--   **Formalization Note** $K$ is chosen before $X$ and $\mathcal B$; $X$ is a finite type.
--
--   Differences from the source:
--   - correction: every non-empty increasing family B (no condition on ℓ(B)) → additionally 2 ≤ ℓ(B); reason: false when ℓ(B) = 1: X = {x}, B = {{x}} is non-empty and increasing, µ_p(B) = p gives p_c(B) = 1/2 and q_f(B) = 1/2, but log ℓ(B) = log 1 = 0, so p_c ≤ K q_f log ℓ reads 1/2 ≤ 0; ℓ(B) ≥ 2 also excludes ∅ ∈ B, where p_c is undefined; the paper uses the theorem only with ℓ(B) = L ≥ 2 (Lemma 8.11, p.44)
--   - encoding: every finite set X → every finite type α : Type; reason: every finite set is in bijection with a finite type Fin m : Type
--   - reading: log (base not named) → natural logarithm Real.log; reason: standard convention; paper.md decision 6
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Theorem 8.9 (quoting [13] Frankston–Kahn–Narayanan–Park), p.43

import Mathlib
import Definitions.Def_HypClass1_IsIncreasing
import Definitions.Def_HypClass1_pc
import Definitions.Def_HypClass1_qf
import Definitions.Def_HypClass1_ellMax

namespace HypClass1

/-- **Theorem 8.9 (fractional Kahn–Kalai, Frankston–Kahn–Narayanan–Park [13], as quoted; corrected:
ℓ(B) ≥ 2).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Theorem 8.9, p.43: "There exists a universal constant K > 0 such that, for every
finite set X and every non-empty increasing family B ⊆ 2^X, p_c(B) ≤ Kq_f(B) log ℓ(B)."

**Correction.** As printed the statement is false when `ℓ(B) = 1`: for `X = {x}`, `B = {{x}}`, one has
`µ_p(B) = p`, so `p_c(B) = 1/2`, and `q_f(B) = 1/2`, while `log ℓ(B) = log 1 = 0`. The hypothesis `ℓ(B) ≥ 2`
is added (it also excludes `∅ ∈ B`, where `p_c` is undefined). The paper uses the theorem only with
`ℓ(B) = L ≥ 2` (Lemma 8.11, p.44).

**Formalization Note.** `K` is chosen before `X` and `B`. The finite set `X` is a finite type `α : Type`
(every finite set is in bijection with some `Fin m : Type`). -/
theorem theorem_8_9 :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : Type) [Fintype α] [DecidableEq α] (B : Finset (Finset α)),
      B.Nonempty → IsIncreasing B → 2 ≤ ellMax B →
      pc B ≤ K * qf B * Real.log (ellMax B) := by sorry

end HypClass1
