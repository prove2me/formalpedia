-- Prove2me | Theorems.Thm_ImplicitParityWL_lemma_4_14
-- name    : ImplicitParityWL.lemma_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:16:48.372657+00:00
-- url     : https://prove2.me/theorems/2f7855e7-b7fb-4f26-97e4-126f88eb976d
-- title:
--   Lemma 4.14 — the counter's first conflict is at round $3\cdot2^{m-1}$
-- statement:
--   For $k\ge3$ and $\ell\ge1$, the implicit parity system $\mathcal I^{k,\ell}_{\mathrm{ctr}}$ satisfies
--   $$
--   \tau(\mathcal I^{k,\ell}_{\mathrm{ctr}})=3\cdot2^{m-1},\qquad m=(k-1)\ell.
--   $$
--   A representation of size polynomial in $2^\ell$ thus has a first conflict at a round exponential in $m$, and this gap is the source of the lower bound.
--
--   **Formalization Note** Since $k\ge3$ and $\ell\ge1$, $m\ge2$, so the subtraction in $\mathbb N$ is exact.
--
--   Differences from the source: none.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Lemma 4.14, p.23

import Mathlib
import Definitions.Def_ImplicitParityWL_Counter

namespace ImplicitParityWL

/-- **Lemma 4.14** (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.23): the counter `ℐ_ctr^{k,ℓ}` has first conflict round `τ(ℐ_ctr^{k,ℓ}) = 3 · 2^{m-1}`,
where `m = (k - 1)ℓ`.

**Formalization Note** The subtractions are in `ℕ`, and `k ≥ 3`, `ℓ ≥ 1` give `m ≥ 2`. -/
theorem lemma_4_14 (k ℓ : ℕ) (hk : 3 ≤ k) (hℓ : 1 ≤ ℓ) :
    (counter k ℓ).toParity.τ = ((3 * 2 ^ ((k - 1) * ℓ - 1) : ℕ) : ℕ∞) := by sorry

end ImplicitParityWL
