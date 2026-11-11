-- Prove2me | Theorems.Thm_ListHashFurstenberg_Main_theorem_2_20
-- name    : ListHashFurstenberg.Main.theorem_2_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:30.259899+00:00
-- url     : https://prove2.me/theorems/b94d10de-cf79-4a99-9cfc-c4b75bdeebae
-- title:
--   Theorem 2.20 — dimension compression of Furstenberg sets and the resulting lower bound
-- statement:
--   Throughout, $F$ is a finite field with $q=|F|$ elements and $F^n$ is the space of length-$n$ vectors over $F$. A set $S\subseteq F^n$ is **$(\delta,n,r,T)$-Furstenberg** if for at least a $\delta$-fraction of all $r$-dimensional linear subspaces $V\le F^n$ there is a shift $x\in F^n$ with $|(x+V)\cap S|\ge T$.
--
--   Let $\delta>0$, let $n\ge k\ge1$ be integers, let $T$ be real with $8q\le T\le q^{n-k}$, and let $t=\lceil\log_qT\rceil$. Suppose $S\subseteq F^n$ is $(\delta,n,n-k,T)$-Furstenberg. Then:
--
--   1. there is a $(\delta/2,\,k+2t,\,2t,\,T)$-Furstenberg set $S'\subseteq F^{k+2t}$ with $|S'|\le|S|$; and
--   2. $$|S|\ge\frac{\delta T}{8}\,q^{k}\exp\!\left(-\frac{8q(k+2t)}{T}\right).$$
--
--   Both parts hold also when $n<k+2t$. The bound depends on $k$ and $T$ but not on the ambient dimension $n$, which is what makes it useful for hashing from large universes and for codes of vanishing rate.
--
--   Differences from the source:
--   - encoding: $\mathbb F_q$ with $q$ a prime power → an arbitrary finite field $F$ with $q=|F|$; reason: every finite field has prime-power order and every prime power is the order of a finite field, so the instances are the same.
-- source:
--   Vinayak M. Kumar, Geoffrey Mon, List Decoding, Linear Hashing, and Furstenberg over F_q, STOC 2027 submission #1578 (October 2026), PDF SHA-256 7cc3a39af88d6de0a57be33c5d8c2855020a7107b6d5e947fb47901273a80ed9, Theorem 2.20, p.19 (formal version of Theorem 1.3, p.6)

import Mathlib
import Definitions.Def_ListHashFurstenberg_Main_Furstenberg

namespace ListHashFurstenberg.Main

/-- Theorem 2.20, p.19 of Kumar–Mon, STOC 2027 submission #1578 (formal Theorem 1.3). Let
`δ > 0`, `n ≥ k ≥ 1`, `8q ≤ T ≤ q^{n-k}` and `t = ⌈log_q T⌉`. If `S ⊆ F^n` is
`(δ, n, n-k, T)`-Furstenberg, then there is a `(δ/2, k+2t, 2t, T)`-Furstenberg set of size at most
`|S|`, and `|S| ≥ (δT/8) · q^k · exp(-8q(k+2t)/T)`. -/
theorem theorem_2_20 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (δ T : ℝ) (hδ : 0 < δ)
    (hT1 : 8 * (Fintype.card F : ℝ) ≤ T) (hT2 : T ≤ (Fintype.card F : ℝ) ^ (n - k))
    (S : Finset (Fin n → F)) (hS : IsFurstenberg δ n (n - k) T S) :
    (∃ S' : Finset (Fin (k + 2 * ⌈Real.logb (Fintype.card F) T⌉₊) → F),
        IsFurstenberg (δ / 2) (k + 2 * ⌈Real.logb (Fintype.card F) T⌉₊)
          (2 * ⌈Real.logb (Fintype.card F) T⌉₊) T S' ∧ S'.card ≤ S.card) ∧
    δ * T / 8 * (Fintype.card F : ℝ) ^ k *
        Real.exp (-(8 * (Fintype.card F : ℝ) *
          (k + 2 * ⌈Real.logb (Fintype.card F) T⌉₊ : ℕ)) / T) ≤ (S.card : ℝ) := by sorry

end ListHashFurstenberg.Main
