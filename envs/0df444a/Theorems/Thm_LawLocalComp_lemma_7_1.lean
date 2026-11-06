-- Prove2me | Theorems.Thm_LawLocalComp_lemma_7_1
-- name    : LawLocalComp.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:13:33.094459+00:00
-- url     : https://prove2.me/theorems/293dfd44-bce7-4b63-8728-f2a2d0fc9712
-- title:
--   Lemma 7.1 (Active residual envelope)
-- statement:
--   Let $X=b+R=b+\Delta K$ be a nonconstant lattice-log-concave law, $p=\mathbb P(R>0)$ and $\nu=\mathbb E[R\mid R>0]$. For every integer $r\ge1$,
--   $$\mathbb P(R\ge3\nu r)\le p\,2^{-r},\qquad \mathbb E[R\mathbf 1\{R\ge3\nu r\}]\le3(r+2)2^{-r}\,\mathbb ER.\tag{30}$$
--   These tail bounds, at the scale of the active mean rather than of the unconditional mean, supply the two budgets of Lemma 7.2.
--
--   **Formalization Note** The law is given with its lattice representation; nonconstant means $h\ge1$.
--
--   Differences from the source: none.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 7.1, (30), p.13, with the setting of §7, p.13

import Mathlib
import Definitions.Def_LawLocalComp_IsLatticeRep
import Definitions.Def_LawLocalComp_IsLCSeq
import Definitions.Def_LawLocalComp_activeMean

namespace LawLocalComp

/-- **Lemma 7.1 (Active residual envelope).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 7.1, (30), p.13, with the setting of §7, p.13 ("Write X = b + R = b + ∆K … For a
nonconstant law let p = P(R > 0) and ν = E[R | R > 0]").

For a nonconstant lattice-log-concave law `X = b + R = b + ΔK`, with `p = P(R > 0)` and
`ν = E[R | R > 0]`, every integer `r ≥ 1` satisfies `P(R ≥ 3νr) ≤ p2^{−r}` and
`E[R 1{R ≥ 3νr}] ≤ 3(r + 2)2^{−r} ER`.

**Formalization Note.** The law is given with its lattice representation; nonconstant is `h ≥ 1`. -/
theorem lemma_7_1 (X : Law) (b Δ : ℚ) (h : ℕ) (p : ℕ → ℚ) (hrep : IsLatticeRep X b Δ h p)
    (hLC : IsLCSeq h p) (hh : 1 ≤ h) (r : ℕ) (hr : 1 ≤ r) :
    (∑ x ∈ X.w.support with 3 * activeMean X b * r ≤ x - b, X.w x) ≤
        activity X b * (2 : ℝ)⁻¹ ^ r ∧
      (∑ x ∈ X.w.support with 3 * activeMean X b * r ≤ x - b, (x - b) * X.w x) ≤
        3 * (r + 2) * (2 : ℝ)⁻¹ ^ r * ∑ x ∈ X.w.support, (x - b) * X.w x := by sorry

end LawLocalComp
