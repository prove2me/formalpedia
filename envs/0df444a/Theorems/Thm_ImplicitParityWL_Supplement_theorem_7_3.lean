-- Prove2me | Theorems.Thm_ImplicitParityWL_Supplement_theorem_7_3
-- name    : ImplicitParityWL.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:30:22.684583+00:00
-- url     : https://prove2.me/theorems/6bdac296-6c10-49a2-9bcb-38170e4eeade
-- title:
--   Theorem 7.3 — the matrix compiler: Spoiler in $O_k(\Lambda(\tau+1))$ rounds, Duplicator survives $\tau-1$
-- statement:
--   Let $k\ge3$ and $\ell\ge1$, let $\mathcal I$ be an implicit parity system with coordinate set $[k]\times\mathbb F_2^\ell$, let $\tau=\tau(\mathcal I)$, and let $\tilde G_0,\tilde G_1$ be the graphs of the matrix construction (§7.1), with $\Lambda=1+\max(\{0\}\cup\{m_e\})$. Then:
--
--   1. if $\tau<\infty$, Spoiler wins the bijective pebble game on $(\tilde G_0,\tilde G_1)$ with $k+1$ pebbles in $O_k(\Lambda(\tau+1))$ rounds;
--   2. Duplicator survives this game for $\tau-1$ rounds, or indefinitely if $\tau=\infty$.
--
--   The matrix compiler trades the mask classes of §5.1, of size $2^{\operatorname{rank}B_e}$, for color classes of size at most four, at the price of the factor $\Lambda$ in Spoiler's bound; it is the compiler used for register programs (Theorem 8.6).
--
--   **Formalization Note** The graphs are those of the definition `ImplicitParityWL.Supplement.MatrixGraph`. The constant of $O_k$ depends on $k$ alone and is chosen before $\ell$, $\mathcal I$ and $\Lambda$. Clause 2 says that Duplicator survives $r$ rounds whenever $r+1\le\tau$ in $\mathbb N\cup\{\infty\}$.
--
--   Differences from the source:
--   - encoding: O_k(Λ(τ + 1)) rounds → ∃ b : ℕ, 0 < b, chosen before ℓ and the system, Spoiler wins within b * Λ * (τ₀ + 1); reason: the constant depends on k alone
--   - encoding: survives τ − 1 rounds, or indefinitely if τ = ∞ → Survives r for all r with r + 1 ≤ τ in ℕ∞; reason: one formula for both cases, without truncated subtraction
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Theorem 7.3, p.39 (construction §7.1, pp.36–37)

import Mathlib
import Definitions.Def_ImplicitParityWL_Supplement_MatrixGraph

namespace ImplicitParityWL

namespace Supplement

/-- **Theorem 7.3** (Matrix compiler; Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the
Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.39): let
`k ≥ 3` and `ℓ ≥ 1`, let `I` be an implicit parity system with coordinate set `[k] × 𝔽₂^ℓ`, `τ := τ(I)`,
and let `G̃₀`, `G̃₁` be the graphs of the matrix construction (§7.1). (I) If `τ < ∞`, then Spoiler wins
the bijective pebble game on `(G̃₀, G̃₁)` with `k + 1` pebbles in `O_k(Λ(τ + 1))` rounds. (II) Duplicator
survives this game for `τ - 1` rounds, or indefinitely if `τ = ∞`.

**Formalization Note** `G̃_ε` is `MatrixSystem.graph I ε` and `Λ = 1 + max({0} ∪ {m_e})` is
`MatrixSystem.Λ I`. The constant `b` of `O_k` depends on `k` alone: it is chosen before `ℓ`, `I` and
`Λ`. Clause (II) is `Survives r` for every `r` with `r + 1 ≤ τ` in `ℕ∞`. -/
theorem theorem_7_3 (k : ℕ) (hk : 3 ≤ k) : ∃ b : ℕ, 0 < b ∧ ∀ ℓ : ℕ, 1 ≤ ℓ →
    ∀ {W E : Type} [Fintype W] [Fintype E] (I : ImplicitSystem k ℓ W E),
      (∀ τ₀ : ℕ, I.toParity.τ = (τ₀ : ℕ∞) →
        SpoilerWinsWithin (k + 1) (MatrixSystem.graph I 0) (MatrixSystem.graph I 1)
          (b * MatrixSystem.Λ I * (τ₀ + 1))) ∧
      (∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.toParity.τ →
        Survives (MatrixSystem.graph I 0) (MatrixSystem.graph I 1) r
          (GameState.empty : GameState _ _ (k + 1))) := by sorry

end Supplement

end ImplicitParityWL
