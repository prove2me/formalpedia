-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_lemma_A_6
-- name    : LpSubspaceCoreset.SmallP.lemma_A_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:46:35.323201+00:00
-- url     : https://prove2.me/theorems/0dc5cdd5-f432-4fd7-801d-12df35ef79d1
-- title:
--   Lemma A.6 — Lipschitz scalar decoder
-- statement:
--   Fix $1\le p\le2$. For $a,b\ge0$ and $\sigma\in\{-1,1\}$ define
--   $$T=a^p,\quad V=b^p,\quad H=p\,\sigma a^{p-1}b,\quad U=|a+\sigma b|^p,$$
--   with $H=0$ when $a=0$ (at $p>1$ the formula already gives $0$). Define $T',V',H',U'$ analogously from $a',b'\ge0$ and $\sigma'\in\{-1,1\}$. There is $C_p$, depending only on $p$, with
--   $$|U-U'|\le C_p\big(|T-T'|+|V-V'|+|H-H'|\big).\qquad(A.15)$$
--   The bound includes sign changes, exact cancellation and zero amplitudes; it recovers the parallel residual power from three scalar coordinates in the proof of Theorem 3.1.
--
--   Differences from the source: none.
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 43, Lemma A.6

import Mathlib

namespace LpSubspaceCoreset.SmallP

/-- **Lemma A.6** (Lipschitz scalar decoder), p. 43.

Fix `1 ≤ p ≤ 2`. For `a, b ≥ 0` and `σ ∈ {−1, 1}` put `T = a^p`, `V = b^p`, `H = pσa^{p−1}b`
(with `H = 0` when `a = 0`; for `p > 1` the formula already gives `0`) and `U = |a + σb|^p`, and
define `T′, V′, H′, U′` analogously from `a′, b′ ≥ 0`, `σ′ ∈ {−1, 1}`. There is `C_p` depending only
on `p` with `|U − U′| ≤ C_p (|T − T′| + |V − V′| + |H − H′|)` (A.15). -/
theorem lemma_A_6 :
    ∀ p : ℝ, 1 ≤ p → p ≤ 2 → ∃ C : ℝ,
    ∀ a b σ a' b' σ' : ℝ, 0 ≤ a → 0 ≤ b → (σ = 1 ∨ σ = -1) →
      0 ≤ a' → 0 ≤ b' → (σ' = 1 ∨ σ' = -1) →
      |(|a + σ * b|) ^ p - (|a' + σ' * b'|) ^ p| ≤
        C * (|a ^ p - a' ^ p| + |b ^ p - b' ^ p| +
          |(if a = 0 then 0 else p * σ * a ^ (p - 1) * b) -
            (if a' = 0 then 0 else p * σ' * a' ^ (p - 1) * b')|) := by sorry

end LpSubspaceCoreset.SmallP
