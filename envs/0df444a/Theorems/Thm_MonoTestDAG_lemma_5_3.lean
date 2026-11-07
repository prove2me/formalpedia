-- Prove2me | Theorems.Thm_MonoTestDAG_lemma_5_3
-- name    : MonoTestDAG.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:09:43.378271+00:00
-- url     : https://prove2.me/theorems/2f6bf089-eae7-4dd0-b9ec-8c28cc2a349a
-- title:
--   Lemma 5.3 — existence of PMRS witnesses with bounded matching exposure
-- statement:
--   There is an absolute constant $\eta_0>0$ with the following property. Fix integers $r\ge t\ge1$. There is a constant $c_{r,t}>0$ such that for all sufficiently large $P$, there is an $(s,\eta_0)$-PMRS graph $U=(L,R;E)$ with an $(s,\eta_0)$-PMRS witness having $(q_0,1/20)$-bounded matching exposure, where, writing $|L|=|R|=n_0$,
--   $$
--   s=P^t,\quad q_0=\Bigl\lfloor c_{r,t}\frac{s}{\log n_0}\Bigr\rfloor,\quad n_0=\Theta_{r,t}(P^{r+t+2}),\quad |E|=\Theta_{r,t}(n_0s).
--   $$
--   These graphs are the source of hardness for the whole lower bound.
--
--   Differences from the source:
--   - encoding: log with no base → `Real.log`; reason: the base is absorbed by c_{r,t}
--   - encoding: Θ_{r,t}, "sufficiently large P" → constants C₁, C₂ > 0 and a threshold P₀ after r, t; reason: Lean form of the page's constants
--   - reading: s ∈ ℕ in Definition 4.3 → s ≥ 1, inside `IsPMRSWitness`; reason: [K] is defined only for positive K (p.1); the index i ∈ [s] and Unif([s]) need s ≥ 1
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Lemma 5.3, p.26

import Mathlib
import Definitions.Def_MonoTestDAG_IsPMRSWitness
import Definitions.Def_MonoTestDAG_exposeSet

namespace MonoTestDAG

/-- **Lemma 5.3 (Existence of PMRS witnesses with bounded matching exposure).** There is an
absolute constant `η₀ > 0` with the following property. Fix integers `r ≥ t ≥ 1`. There is a
constant `c_{r,t} > 0` such that, for all sufficiently large `P`, there is an `(s, η₀)`-PMRS graph
`U = (L, R; E)` with an `(s, η₀)`-PMRS witness `M = (M_1, …, M_s)` having `(q₀, 1/20)`-bounded
matching exposure, where, writing `|L| = |R| = n₀`,
`s = P^t`, `q₀ = ⌊c_{r,t} s / log n₀⌋`, `n₀ = Θ_{r,t}(P^{r+t+2})`, `|E| = Θ_{r,t}(n₀ s)`.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Lemma 5.3, p.26.

**Formalization Note.** `log` is the natural logarithm (the base is absorbed into `c_{r,t}`). The
`Θ_{r,t}` are constants `C₁, C₂ > 0` depending on `r, t`; the threshold `P₀` depends on
`r, t`. -/
theorem lemma_5_3 :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ r t : ℕ, 1 ≤ t → t ≤ r →
      ∃ c : ℝ, 0 < c ∧ ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P →
        ∃ (L R : Type) (_ : Fintype L) (_ : Fintype R) (_ : DecidableEq L) (_ : DecidableEq R)
          (EU : Finset (L × R)) (M : Fin (P ^ t) → Finset (L × R)),
          IsPMRSWitness EU η₀ (P ^ t) M ∧
          HasBoundedExposure M ⌊c * ((P ^ t : ℕ) : ℝ) / Real.log (Fintype.card L : ℝ)⌋₊ (1 / 20) ∧
          C₁ * (P : ℝ) ^ (r + t + 2) ≤ (Fintype.card L : ℝ) ∧
          (Fintype.card L : ℝ) ≤ C₂ * (P : ℝ) ^ (r + t + 2) ∧
          C₁ * (Fintype.card L : ℝ) * ((P ^ t : ℕ) : ℝ) ≤ (EU.card : ℝ) ∧
          (EU.card : ℝ) ≤ C₂ * (Fintype.card L : ℝ) * ((P ^ t : ℕ) : ℝ) := by sorry

end MonoTestDAG
