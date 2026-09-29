-- Prove2me | Theorems.Thm_IPProximity_Eisenbrand_partial_sum_pigeonhole
-- name    : IPProximity.Eisenbrand.partial_sum_pigeonhole
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:32:49.550683+00:00
-- url     : https://prove2.me/theorems/d2ea6ca6-0450-4301-b1c5-c66edf2cc25b
-- title:
--   Proof of Theorem 3.3, Eq. (20) — counting partial sums
-- statement:
--   Let $m,\Delta,L\in\mathbb N$ and let $p_1,\dots,p_L\in\mathbb Z^m$ be integer vectors with $\|p_k\|_\infty\le m\cdot\Delta$ for every $k$. If no vector occurs among $p_1,\dots,p_L$ more than $m$ times (there are no indices $k_1<\dots<k_{m+1}$ with $p_{k_1}=\dots=p_{k_{m+1}}$), then
--   $$L\le m\cdot(2\cdot m\cdot\Delta+1)^m .$$
--
--   In the proof of Theorem 3.3 the $p_k$ are the partial sums (19) of the rearranged Steinitz sequence and $L=t+m\ge\|z^*-x^*\|_1$; the bound counts the $(2m\Delta+1)^m$ integer points of $\ell_\infty$-norm at most $m\Delta$.
-- source:
--   Eisenbrand & Weismantel, Proximity Results and Faster Algorithms for Integer Programming Using the Steinitz Lemma, ACM Trans. Algorithms 16(1), Article 5 (2019), p. 5:9, proof of Theorem 3.3, Eq. (19)–(20)

import Mathlib

namespace IPProximity.Eisenbrand

/-- Proof of Theorem 3.3, Eq. (19)–(20) (p. 5:9): a sequence `p₁, …, p_L` of integer vectors in
`ℤᵐ` of `ℓ∞`-norm at most `m·Δ` in which no value occurs `m + 1` times has length
`L ≤ m·(2mΔ + 1)ᵐ`. -/
theorem partial_sum_pigeonhole {m L : ℕ} (Δ : ℕ) (p : Fin L → Fin m → ℤ)
    (hp : ∀ k i, |p k i| ≤ (m : ℤ) * Δ)
    (hmult : ∀ v : Fin m → ℤ, (Finset.univ.filter (fun k : Fin L => p k = v)).card ≤ m) :
    L ≤ m * (2 * m * Δ + 1) ^ m := by sorry

end IPProximity.Eisenbrand
