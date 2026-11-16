-- Prove2me | Theorems.Thm_ImplicitParityWL_Supplement_theorem_2_5
-- name    : ImplicitParityWL.Supplement.theorem_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:29:45.911923+00:00
-- url     : https://prove2.me/theorems/9b6894e9-c25c-4b01-998e-f4628e271c2d
-- title:
--   Theorem 2.5 — graph compiler with the size bound (4)
-- statement:
--   Let $k\ge3$ and $\ell\ge1$, let $\mathcal I=(W,\mathfrak c,(\mathfrak c_v)_{v\in W},\mathcal E,\iota)$ be an implicit parity system with coordinate set $\mathfrak c=[k]\times\mathbb F_2^\ell$, and let $\tau=\tau(\mathcal I)$. Then there is a pair of colored graphs $(G_0,G_1)$ such that:
--
--   1. if $\tau<\infty$, Spoiler wins the bijective pebble game on $(G_0,G_1)$ with $k+1$ pebbles in $O_k(\tau+1)$ rounds;
--   2. Duplicator survives this game for $\tau-1$ rounds, or indefinitely if $\tau=\infty$;
--   3. each of the two graphs has at most
--   $$N=O\Bigl(\sum_{v\in W}|\mathfrak c_v|+(k+1)\sum_{e\in\mathcal E}\bigl(|\mathfrak c_e|+2^{\operatorname{rank}B_e}\bigr)\Bigr)\tag{4}$$
--   vertices, where $B_e$ is the check matrix restricted to the columns of $\mathfrak c_e$.
--
--   This is the paper's key technical result: it turns the conflict round of a succinct parity system into the number of pebble-game rounds, with graphs of size close to the description of the system.
--
--   **Formalization Note** The constant of (4) is absolute and chosen before $k$; the constant $b$ of $O_k$ depends on $k$ alone and is chosen before $\ell$ and $\mathcal I$. Clause 2 says that Duplicator survives $r$ rounds whenever $r+1\le\tau$ in $\mathbb N\cup\{\infty\}$. The rank is over $\mathbb F_2$.
--
--   Differences from the source:
--   - encoding: O_k(τ + 1) rounds → ∃ b : ℕ, 0 < b, chosen before ℓ and the system, Spoiler wins within b * (τ₀ + 1); reason: the constant depends on k alone, as in the published Theorem 5.2
--   - encoding: survives τ − 1 rounds, or indefinitely if τ = ∞ → Survives r for all r with r + 1 ≤ τ in ℕ∞; reason: one formula for both cases, without truncated subtraction
--   - reading: N = O(…) for the number of vertices in both graphs → one absolute C, chosen before k, bounding |V₀| and |V₁| separately; reason: the factor (k + 1) in (4) is explicit, so the hidden constant is absolute; the stronger reading
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Theorem 2.5 and eq. (4), p.12

import Mathlib
import Definitions.Def_ImplicitParityWL_ImplicitSystem
import Definitions.Def_ImplicitParityWL_CheckMatrix
import Definitions.Def_ImplicitParityWL_PebbleGame

namespace ImplicitParityWL

namespace Supplement

/-- **Theorem 2.5** (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman
Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.12): let `k ≥ 3` and `ℓ ≥ 1`,
let `I` be an implicit parity system with coordinate set `[k] × 𝔽₂^ℓ`, and let `τ := τ(I)`. Then there is
a pair of colored graphs `(G₀, G₁)` such that (I) if `τ < ∞`, Spoiler wins the bijective pebble game on
`(G₀, G₁)` with `k + 1` pebbles in `O_k(τ + 1)` rounds; (II) Duplicator survives this game for `τ - 1`
rounds, or indefinitely if `τ = ∞`. Moreover, the number of vertices in both graphs is at most
`N = O(∑_{v ∈ W} |𝔠_v| + (k + 1) ∑_{e ∈ E} (|𝔠_e| + 2^{rank B_e}))`, eq. (4).

**Formalization Note** The constant `C` of the size bound (4) is absolute (chosen before `k`, the factor
`k + 1` being explicit); the constant `b` of `O_k` depends on `k` alone (chosen before `ℓ` and `I`).
Clause (II) is `Survives r` for every `r` with `r + 1 ≤ τ` in `ℕ∞`. `B_e` is the published
`restrictedCheck` of the schema's domain, and its rank is taken over `𝔽₂`. Each graph's vertex count is
bounded separately. -/
theorem theorem_2_5 : ∃ C : ℕ, ∀ k : ℕ, 3 ≤ k → ∃ b : ℕ, 0 < b ∧ ∀ ℓ : ℕ, 1 ≤ ℓ →
    ∀ {W E : Type} [Fintype W] [Fintype E] (I : ImplicitSystem k ℓ W E),
      ∃ (K V₀ V₁ : Type) (_ : Fintype V₀) (_ : Fintype V₁) (G₀ : ColoredGraph K V₀)
        (G₁ : ColoredGraph K V₁),
        (∀ τ₀ : ℕ, I.toParity.τ = (τ₀ : ℕ∞) → SpoilerWinsWithin (k + 1) G₀ G₁ (b * (τ₀ + 1))) ∧
        (∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.toParity.τ →
          Survives G₀ G₁ r (GameState.empty : GameState V₀ V₁ (k + 1))) ∧
        Fintype.card V₀ ≤ C * (∑ v, (I.dom v).card + (k + 1) * ∑ e,
          ((I.schema e).dom.card + 2 ^ (restrictedCheck (I.schema e).dom).rank)) ∧
        Fintype.card V₁ ≤ C * (∑ v, (I.dom v).card + (k + 1) * ∑ e,
          ((I.schema e).dom.card + 2 ^ (restrictedCheck (I.schema e).dom).rank)) := by sorry

end Supplement

end ImplicitParityWL
