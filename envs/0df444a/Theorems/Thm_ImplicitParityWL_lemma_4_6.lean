-- Prove2me | Theorems.Thm_ImplicitParityWL_lemma_4_6
-- name    : ImplicitParityWL.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:10:39.34502+00:00
-- url     : https://prove2.me/theorems/ca3885ea-57c4-4d34-b5f8-e78a8b44b13f
-- title:
--   Lemma 4.6 — addresses are at Hamming distance at least four
-- statement:
--   Fix $k\ge3$ and $\ell\ge1$. Every two distinct addresses $a,a'\in\Sigma$ have Hamming distance at least four. For every $I\subseteq\mathfrak c$ with $|I|\le k+1$, at most one address $a\in\Sigma$ satisfies $\mathrm{supp}(a)\subseteq I$.
--
--   The second claim is what keeps $k+1$ pebbles from exposing more than one variable per location.
--
--   Differences from the source: none.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Lemma 4.6, p.19

import Mathlib
import Definitions.Def_ImplicitParityWL_Address

namespace ImplicitParityWL

/-- **Lemma 4.6** (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.19): every two distinct addresses have Hamming distance at least four, and for every
`I ⊆ 𝔠` with `|I| ≤ k + 1`, at most one address `a` satisfies `supp(a) ⊆ I`.

**Formalization Note** The Hamming distance is that of the indicator vectors (`Address.word`). -/
theorem lemma_4_6 (k ℓ : ℕ) (hk : 3 ≤ k) (hℓ : 1 ≤ ℓ) :
    (∀ a a' : Address k ℓ, a ≠ a' → 4 ≤ hammingDist a.word a'.word) ∧
    (∀ I : Finset (Coord k ℓ), I.card ≤ k + 1 → ∀ a a' : Address k ℓ,
      a.supp ⊆ I → a'.supp ⊆ I → a = a') := by sorry

end ImplicitParityWL
