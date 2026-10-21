-- Prove2me | Theorems.Thm_HawkesParking_Spine_lemma_1
-- name    : HawkesParking.Spine.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:55.703739+00:00
-- url     : https://prove2.me/theorems/afd19fcc-1a5a-4e37-896b-472e39f756aa
-- title:
--   Lemma 1, p. 9 — there are $(k+1)^{k-1}$ parking functions of length $k$
-- statement:
--   Let $k\ge 1$ and let $\mathsf{PF}_k$ be the set of parking functions of length $k$: vectors $\pi\in\mathbb Z_+^k$ whose increasing rearrangement satisfies $\vec\pi_{(i)}\le i$ for every $i\in\{1,\dots,k\}$. Then
--   $$|\mathsf{PF}_k|=(k+1)^{k-1}.$$
--
--   This count (Pollak's circle argument) fixes the normalizing constant of the uniform distribution on parking functions and enters the probabilities of Proposition 3.
--
--   **Formalization Note.** The hypothesis $k\ge 1$ is the page's $k\in\mathbb Z_+$; it also keeps the natural-number exponent $k-1$ from truncating at $k=0$.
-- source:
--   Daw, Conditional Uniformity and Hawkes Processes, arXiv:2202.05335v2, p. 9, Lemma 1

import Mathlib
import Definitions.Def_HawkesParking_Spine_Model

namespace HawkesParking.Spine
theorem lemma_1 (k : ℕ) (hk : 1 ≤ k) :
    (parkingFunctions k).card = (k + 1) ^ (k - 1) := by sorry
end HawkesParking.Spine
