-- Prove2me | Theorems.Thm_ListHashFurstenberg_Main_theorem_2_8
-- name    : ListHashFurstenberg.Main.theorem_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:26.596816+00:00
-- url     : https://prove2.me/theorems/6dad0acf-7888-4d16-9a43-ee78cc1e0aa8
-- title:
--   Theorem 2.8 — multiplicity-gap lower bound for Furstenberg sets, for every $\varepsilon\in(0,1]$
-- statement:
--   Throughout, $F$ is a finite field with $q=|F|$ elements and $F^n$ is the space of length-$n$ vectors over $F$. A set $S\subseteq F^n$ is **$(\delta,n,r,T)$-Furstenberg** if for at least a $\delta$-fraction of all $r$-dimensional linear subspaces $V\le F^n$ there is a shift $x\in F^n$ with $|(x+V)\cap S|\ge T$.
--
--   Let $n\ge1$, $\delta\ge0$, $\alpha\ge0$, and let $S\subseteq F^n$ be $(\delta,n,r,\alpha q^r)$-Furstenberg. For every real $0<\varepsilon\le1$ put $\beta_\varepsilon=\alpha+(1-\varepsilon)(1-\alpha)$ and
--
--   $$A=\frac{\delta\beta_\varepsilon q^r}{\delta q^r+q-1}.$$
--
--   Then
--
--   1. $$|S|\ge q^n\cdot\frac{A^n-(1-\varepsilon)^n}{1-(1-\varepsilon)^n};$$
--   2. equivalently, the complement $\overline S=F^n\setminus S$ satisfies $$|\overline S|\le q^n\cdot\frac{1-A^n}{1-(1-\varepsilon)^n};$$
--   3. and this right-hand side equals $$q^n\cdot\frac{1-\Big(1-\frac{\delta\varepsilon(1-\alpha)q^r+q-1}{\delta q^r+q-1}\Big)^n}{1-(1-\varepsilon)^n}.$$
--
--   The bound comes from the polynomial method with multiplicity gaps: high multiplicity is imposed on $S$ and a smaller multiplicity on its complement. Corollary 2.14 optimizes it over $\varepsilon$.
--
--   Differences from the source:
--   - encoding: $\mathbb F_q$ with $q$ a prime power → an arbitrary finite field $F$ with $q=|F|$; reason: every finite field has prime-power order and every prime power is the order of a finite field, so the instances are the same.
--   - reading: a $\delta$-fraction of subspaces and the threshold $\alpha q^r$, with no range stated → hypotheses $\delta\ge0$ and $\alpha\ge0$; reason: $\delta$ is a fraction of subspaces and $\alpha$ the fraction of the $q^r$ points of a translate; for negative $\delta$ or $\alpha$ the empty set is Furstenberg and the displayed bound fails (e.g. $\varepsilon=1$, very negative $\alpha$, even $n$), so the printed theorem only makes sense for these ranges. Values above $1$ are allowed: they make the hypothesis unsatisfiable or the bound weaker.
--   - encoding: $S\subset\mathbb F_q^n$ with $n$ implicit → hypothesis $n\ge1$; reason: at $n=0$ the denominator $1-(1-\varepsilon)^0$ is $0$ and the quotient is undefined.
--   - encoding: "or equivalently" and the displayed rewrite → the three displays stated as a conjunction; reason: the source asserts all three.
-- source:
--   Vinayak M. Kumar, Geoffrey Mon, List Decoding, Linear Hashing, and Furstenberg over F_q, STOC 2027 submission #1578 (October 2026), PDF SHA-256 7cc3a39af88d6de0a57be33c5d8c2855020a7107b6d5e947fb47901273a80ed9, Theorem 2.8, p.13 (proof pp.13–16)

import Mathlib
import Definitions.Def_ListHashFurstenberg_Main_Furstenberg

namespace ListHashFurstenberg.Main

/-- Theorem 2.8, p.13 of Kumar–Mon, STOC 2027 submission #1578 (multiplicity-gap bound).
Let `S ⊆ F^n` be `(δ, n, r, αq^r)`-Furstenberg, `0 < ε ≤ 1`, `β_ε = α + (1-ε)(1-α)` and
`A = δ β_ε q^r / (δ q^r + q - 1)`. Then `|S| ≥ q^n (A^n - (1-ε)^n) / (1 - (1-ε)^n)`, equivalently
`|F^n \ S| ≤ q^n (1 - A^n) / (1 - (1-ε)^n)`, and the latter numerator equals
`1 - (1 - (δε(1-α)q^r + q - 1)/(δq^r + q - 1))^n`. -/
theorem theorem_2_8 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n r : ℕ) (hn : 1 ≤ n) (δ α ε : ℝ) (hδ : 0 ≤ δ) (hα : 0 ≤ α)
    (S : Finset (Fin n → F))
    (hS : IsFurstenberg δ n r (α * (Fintype.card F : ℝ) ^ r) S)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (Fintype.card F : ℝ) ^ n *
        ((δ * (α + (1 - ε) * (1 - α)) * (Fintype.card F : ℝ) ^ r /
            (δ * (Fintype.card F : ℝ) ^ r + Fintype.card F - 1)) ^ n - (1 - ε) ^ n) /
        (1 - (1 - ε) ^ n) ≤ (S.card : ℝ) ∧
    ((Finset.univ \ S).card : ℝ) ≤
      (Fintype.card F : ℝ) ^ n *
        (1 - (δ * (α + (1 - ε) * (1 - α)) * (Fintype.card F : ℝ) ^ r /
            (δ * (Fintype.card F : ℝ) ^ r + Fintype.card F - 1)) ^ n) /
        (1 - (1 - ε) ^ n) ∧
    (Fintype.card F : ℝ) ^ n *
        (1 - (δ * (α + (1 - ε) * (1 - α)) * (Fintype.card F : ℝ) ^ r /
            (δ * (Fintype.card F : ℝ) ^ r + Fintype.card F - 1)) ^ n) /
        (1 - (1 - ε) ^ n) =
      (Fintype.card F : ℝ) ^ n *
        (1 - (1 - (δ * ε * (1 - α) * (Fintype.card F : ℝ) ^ r + Fintype.card F - 1) /
            (δ * (Fintype.card F : ℝ) ^ r + Fintype.card F - 1)) ^ n) /
        (1 - (1 - ε) ^ n) := by sorry

end ListHashFurstenberg.Main
