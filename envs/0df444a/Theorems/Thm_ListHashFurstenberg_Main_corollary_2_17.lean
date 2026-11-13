-- Prove2me | Theorems.Thm_ListHashFurstenberg_Main_corollary_2_17
-- name    : ListHashFurstenberg.Main.corollary_2_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:24.028338+00:00
-- url     : https://prove2.me/theorems/b550a4fb-10e4-4662-bba3-aa7c93fe6076
-- title:
--   Corollary 2.17 — Furstenberg lower bound with linear dependence on $\delta$
-- statement:
--   Throughout, $F$ is a finite field with $q=|F|$ elements and $F^n$ is the space of length-$n$ vectors over $F$. A set $S\subseteq F^n$ is **$(\delta,n,r,T)$-Furstenberg** if for at least a $\delta$-fraction of all $r$-dimensional linear subspaces $V\le F^n$ there is a shift $x\in F^n$ with $|(x+V)\cap S|\ge T$.
--
--   Let $S\subseteq F^n$ be $(\delta,n,r,T)$-Furstenberg. As long as $T\ge8q$,
--
--   $$|S|\ge\frac{\delta T}{4}\,q^{\,n-r}\exp\!\left(-\frac{8qn}{T}\right).$$
--
--   Compared with Corollary 2.14 the direction density $\delta$ appears only as a linear factor, not inside the exponential; Theorem 2.20 applies this bound after compressing the dimension.
--
--   Differences from the source:
--   - encoding: $\mathbb F_q$ with $q$ a prime power → an arbitrary finite field $F$ with $q=|F|$; reason: every finite field has prime-power order and every prime power is the order of a finite field, so the instances are the same.
--   - encoding: $q^{n-r}$ → the integer power $q^{(n:\mathbb Z)-r}$; reason: no truncated natural-number subtraction; for $\delta>0$ the hypothesis forces $r\le n$, where the two agree.
-- source:
--   Vinayak M. Kumar, Geoffrey Mon, List Decoding, Linear Hashing, and Furstenberg over F_q, STOC 2027 submission #1578 (October 2026), PDF SHA-256 7cc3a39af88d6de0a57be33c5d8c2855020a7107b6d5e947fb47901273a80ed9, Corollary 2.17, p.18

import Mathlib
import Definitions.Def_ListHashFurstenberg_Main_Furstenberg

namespace ListHashFurstenberg.Main

/-- Corollary 2.17, p.18 of Kumar–Mon, STOC 2027 submission #1578. Let `S ⊆ F^n` be
`(δ, n, r, T)`-Furstenberg. As long as `T ≥ 8q`, `|S| ≥ (δT/4) · q^{n-r} · exp(-8qn/T)`. -/
theorem corollary_2_17 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n r : ℕ) (δ T : ℝ) (S : Finset (Fin n → F)) (hS : IsFurstenberg δ n r T S)
    (hT : 8 * (Fintype.card F : ℝ) ≤ T) :
    δ * T / 4 * (Fintype.card F : ℝ) ^ ((n : ℤ) - r) *
        Real.exp (-(8 * (Fintype.card F : ℝ) * n) / T) ≤ (S.card : ℝ) := by sorry

end ListHashFurstenberg.Main
