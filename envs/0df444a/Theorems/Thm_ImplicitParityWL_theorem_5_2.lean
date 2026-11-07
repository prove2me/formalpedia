-- Prove2me | Theorems.Thm_ImplicitParityWL_theorem_5_2
-- name    : ImplicitParityWL.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:18:40.340975+00:00
-- url     : https://prove2.me/theorems/9643f09a-9118-4b6e-a320-3bda80110cf6
-- title:
--   Theorem 5.2 — pebble rounds of $(G_0,G_1)$ track the first conflict round $\tau$
-- statement:
--   Let $k\ge3$ and $\ell\ge1$, let $\mathcal I$ be an implicit parity system with coordinate set $[k]\times\mathbb F_2^\ell$, let $\tau=\tau(\mathcal I)$, and let $G_0,G_1$ be the graphs constructed from the system. Then:
--
--   1. if $\tau<\infty$, then Spoiler wins the bijective pebble game on $(G_0,G_1)$ with $k+1$ pebbles in $O_k(\tau+1)$ rounds;
--   2. Duplicator survives this game for $\tau-1$ rounds, or indefinitely if $\tau=\infty$.
--
--   This is the paper's main compiler theorem: it holds for every implicit parity system, including those with ternary schemas, although the counter uses only binary ones.
--
--   **Formalization Note** The constant of $O_k$ depends on $k$ alone. Clause 2 says that Duplicator survives $r$ rounds for every $r$ with $r+1\le\tau$ in $\mathbb N\cup\{\infty\}$.
--
--   Differences from the source:
--   - encoding: O_k(τ + 1) rounds → ∃ b : ℕ, 0 < b, chosen before ℓ and the system, Spoiler wins within b * (τ₀ + 1); reason: a natural constant loses nothing against a real one
--   - encoding: survives τ − 1 rounds, or indefinitely if τ = ∞ → Survives r for all r with r + 1 ≤ τ in ℕ∞; reason: one formula for both cases, without truncated subtraction
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Theorem 5.2, p.26

import Mathlib
import Definitions.Def_ImplicitParityWL_CompiledGraph

namespace ImplicitParityWL

/-- **Theorem 5.2** (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.26): let `k ≥ 3` and `ℓ ≥ 1`, let `I` be an implicit parity system with coordinate set
`[k] × 𝔽₂^ℓ`, `τ := τ(I)`, and let `G₀`, `G₁` be the graphs constructed from it. (I) If `τ < ∞`, then Spoiler wins the
bijective pebble game on `(G₀, G₁)` with `k + 1` pebbles in `O_k(τ + 1)` rounds. (II) Duplicator survives this game for
`τ - 1` rounds, or indefinitely if `τ = ∞`.

**Formalization Note** The constant `b` of `O_k` depends on `k` alone: it is chosen before `ℓ` and `I`. Clause (II) says
`Survives r` for all `r` with `r + 1 ≤ τ` in `ℕ∞`, which covers `τ = ∞`. -/
theorem theorem_5_2 (k : ℕ) (hk : 3 ≤ k) : ∃ b : ℕ, 0 < b ∧ ∀ (ℓ : ℕ), 1 ≤ ℓ →
    ∀ {W E : Type} [Fintype W] [Fintype E] (I : ImplicitSystem k ℓ W E),
      (∀ τ₀ : ℕ, I.toParity.τ = (τ₀ : ℕ∞) →
        SpoilerWinsWithin (k + 1) (I.graph 0) (I.graph 1) (b * (τ₀ + 1))) ∧
      (∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.toParity.τ →
        Survives (I.graph 0) (I.graph 1) r (GameState.empty : GameState _ _ (k + 1))) := by sorry

end ImplicitParityWL
