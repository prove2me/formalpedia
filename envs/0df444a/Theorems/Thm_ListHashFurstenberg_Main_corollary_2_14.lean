-- Prove2me | Theorems.Thm_ListHashFurstenberg_Main_corollary_2_14
-- name    : ListHashFurstenberg.Main.corollary_2_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:21.671656+00:00
-- url     : https://prove2.me/theorems/0c22fc1a-79ef-4464-b344-710fcbba693e
-- title:
--   Corollary 2.14 — optimized multiplicity-gap lower bound for Furstenberg sets
-- statement:
--   Throughout, $F$ is a finite field with $q=|F|$ elements and $F^n$ is the space of length-$n$ vectors over $F$. A set $S\subseteq F^n$ is **$(\delta,n,r,T)$-Furstenberg** if for at least a $\delta$-fraction of all $r$-dimensional linear subspaces $V\le F^n$ there is a shift $x\in F^n$ with $|(x+V)\cap S|\ge T$.
--
--   Let $S\subseteq F^n$ be $(\delta,n,r,\alpha q^r)$-Furstenberg. For every real $C$ with $1<C\le\alpha\delta q^{r-1}/2$,
--
--   $$\frac{|S|}{q^n}\ge\exp\!\left(-\frac{2Cn}{\delta\alpha q^{r-1}}\right)\left(1-\frac1C\right)\alpha.$$
--
--   This is Theorem 2.8 with the free parameter $\varepsilon$ chosen well; Corollary 2.17 uses it with $C=2$.
--
--   Differences from the source:
--   - encoding: $\mathbb F_q$ with $q$ a prime power → an arbitrary finite field $F$ with $q=|F|$; reason: every finite field has prime-power order and every prime power is the order of a finite field, so the instances are the same.
--   - encoding: $q^{r-1}$ → the integer power $q^{(r:\mathbb Z)-1}$; reason: no truncated natural-number subtraction, so $r=0$ gives $q^{-1}$ as in the source.
-- source:
--   Vinayak M. Kumar, Geoffrey Mon, List Decoding, Linear Hashing, and Furstenberg over F_q, STOC 2027 submission #1578 (October 2026), PDF SHA-256 7cc3a39af88d6de0a57be33c5d8c2855020a7107b6d5e947fb47901273a80ed9, Corollary 2.14, p.16

import Mathlib
import Definitions.Def_ListHashFurstenberg_Main_Furstenberg

namespace ListHashFurstenberg.Main

/-- Corollary 2.14, p.16 of Kumar–Mon, STOC 2027 submission #1578. Let `S ⊆ F^n` be
`(δ, n, r, αq^r)`-Furstenberg. For all `1 < C ≤ αδq^{r-1}/2`,
`|S| / q^n ≥ exp(-2Cn / (δαq^{r-1})) · (1 - 1/C) · α`. -/
theorem corollary_2_14 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n r : ℕ) (δ α C : ℝ) (S : Finset (Fin n → F))
    (hS : IsFurstenberg δ n r (α * (Fintype.card F : ℝ) ^ r) S)
    (hC1 : 1 < C) (hC2 : C ≤ α * δ * (Fintype.card F : ℝ) ^ ((r : ℤ) - 1) / 2) :
    Real.exp (-(2 * C * n) / (δ * α * (Fintype.card F : ℝ) ^ ((r : ℤ) - 1))) *
        (1 - 1 / C) * α ≤
      (S.card : ℝ) / (Fintype.card F : ℝ) ^ n := by sorry

end ListHashFurstenberg.Main
