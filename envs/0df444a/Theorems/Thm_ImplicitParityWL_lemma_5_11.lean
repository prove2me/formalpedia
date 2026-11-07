-- Prove2me | Theorems.Thm_ImplicitParityWL_lemma_5_11
-- name    : ImplicitParityWL.lemma_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:19:24.151489+00:00
-- url     : https://prove2.me/theorems/94d80b09-638c-4985-88bd-0409f1e272b3
-- title:
--   Lemma 5.11 — extending exposed values
-- statement:
--   Let $\mathcal A'=\mathcal A\cup\{A\}$ with $|\mathcal A|\le k$, and let $r\ge1$ with $K_r$ conflict-free. Every assignment $\alpha:\mathrm{Var}(\mathcal A)\to\mathbb F_2$ that satisfies its exposed equations and agrees with $K_r$ extends to an assignment $\alpha':\mathrm{Var}(\mathcal A')\to\mathbb F_2$ satisfying its exposed equations and agreeing with $K_{r-1}$.
--
--   One game round thus costs one propagation round, which gives Duplicator's bound.
--
--   **Formalization Note** The page's round $r\ge1$ is `r + 1` in Lean, so $K_{r-1}$ is `K r`.
--
--   Differences from the source:
--   - encoding: α : Var(𝒜) → 𝔽₂ and α′ : Var(𝒜′) → 𝔽₂ → total functions on all variables, of which those values are read; extension is agreement on Var(𝒜); reason: the same assignments
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Lemma 5.11, p.32

import Mathlib
import Definitions.Def_ImplicitParityWL_Exposure

namespace ImplicitParityWL

/-- **Lemma 5.11** (Extending exposed values; Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.32): let `A' = A ∪ {A₀}` with `|A| ≤ k`, and let `r ≥ 1` with `K_r`
conflict-free. Every assignment `α : Var(A) → 𝔽₂` that satisfies its exposed equations and agrees with `K_r` extends to an
assignment `α' : Var(A') → 𝔽₂` satisfying its exposed equations and agreeing with `K_{r-1}`.

**Formalization Note** The round `r ≥ 1` of the page is `r + 1` here, so `K_{r-1}` is `K r`. -/
theorem lemma_5_11 (k ℓ : ℕ) (hk : 3 ≤ k) (hℓ : 1 ≤ ℓ) {W E : Type} [Fintype W] [Fintype E]
    [DecidableEq (CColor k ℓ W E)] (I : ImplicitSystem k ℓ W E) (A : Finset (CColor k ℓ W E))
    (hA : A.card ≤ k) (A₀ : CColor k ℓ W E) (r : ℕ) (hr : I.toParity.ConflictFree (r + 1))
    (α : W × Address k ℓ → ZMod 2) (hsat : I.SatisfiesExposed A α) (hagree : I.AgreesWith A α (r + 1)) :
    ∃ α' : W × Address k ℓ → ZMod 2, (∀ X ∈ I.Var A, α' X = α X) ∧
      I.SatisfiesExposed (insert A₀ A) α' ∧ I.AgreesWith (insert A₀ A) α' r := by sorry

end ImplicitParityWL
