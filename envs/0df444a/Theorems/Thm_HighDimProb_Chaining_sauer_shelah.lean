-- Prove2me | Theorems.Thm_HighDimProb_Chaining_sauer_shelah
-- name    : HighDimProb.Chaining.sauer_shelah
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:04:32.843917+00:00
-- url     : https://prove2.me/theorems/f23143a7-f448-4fea-b7f7-5f80a36a6376
-- title:
--   Theorem 8.3.16 — Sauer-Shelah Lemma
-- statement:
--   This is the **Sauer-Shelah Lemma**, a purely combinatorial bound (no probability involved)
--   that controls the size of a finite class of Boolean functions in terms of its VC dimension —
--   the milestone Dudley's inequality (Theorem 8.1.3) is applied through, via the covering-number
--   bound of Theorem 8.3.18 (Section 8.3.4), to obtain a uniform law of large numbers for classes
--   of bounded VC dimension.
--
--   Let $F$ be a class of Boolean functions on a finite set $\Omega$ with $n := |\Omega|$ points,
--   and let $d := \mathrm{vc}(F)$ be its VC dimension (`VcDim`). Then
--
--   $$
--   |F| \;\le\; \sum_{k=0}^{d} \binom{n}{k} \;\le\; \left(\frac{en}{d}\right)^{d}.
--   $$
--
--   The first inequality follows from Pajor's Lemma (that $|F|$ is bounded by the number of
--   subsets of $\Omega$ shattered by $F$, each of size at most $d$ by definition of VC dimension);
--   the second is the standard bound on a partial binomial sum.
--
--   **Formalization Note** $\Omega$ is a `Fintype`, $F$ a `Finset (Ω → Bool)` (automatically
--   finite, since `Ω → Bool` is finite), and $d$ is `(vcDim (F : Set (Ω → Bool))).toNat`: `vcDim`
--   is automatically finite here (every shattered $\Lambda \subseteq \Omega$ has cardinality
--   $\le n$), so no separate finiteness hypothesis is added. At $d=0$, the second bound's `en/d`
--   divides by zero under Lean's convention $x/0=0$, but the exponent $d=0$ still forces
--   $(en/d)^0 = 1$ (Lean's convention $x^0=1$ for every $x$, including this junk value), which
--   is exactly the book's own correct bound $|F| \le 1$ at VC dimension $0$ — not a vacuous
--   statement.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 205, Theorem 8.3.16

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim

namespace HighDimProb.Chaining

/-- **Theorem 8.3.16** (Sauer-Shelah Lemma), Vershynin, *High-Dimensional Probability* (2018),
p. 205 (PDF p. 213).

"Let `F` be a class of Boolean functions on an `n`-point set `Ω`. Then `|F| ≤ ∑_{k=0}^d (n choose
k) ≤ (en/d)^d` where `d = vc(F)`." Here `Ω` is a finite type (the "`n`-point set", `n :=
Fintype.card Ω`), `F` a `Finset` of Boolean functions on `Ω` (automatically finite since `Ω →
Bool` is finite), and `d := (vcDim (F : Set (Ω → Bool))).toNat`: `vcDim` is always finite here
since every shattered `Λ ⊆ Ω` has `Λ.encard ≤ (Fintype.card Ω : ℕ∞) < ⊤`, so `toNat` recovers the
same natural number the book calls `d` without any extra finiteness hypothesis. At `d = 0` the
second bound's `en/d` divides by zero (Lean's convention `x / 0 = 0`), but the exponent `d = 0`
still forces `(en/d)^0 = 1` regardless (Lean's convention `x^0 = 1`), which is exactly the correct
non-vacuous bound `|F| ≤ 1` at VC dimension `0` (footnote-free, since the book's own proof of the
second inequality goes through the binomial-sum bound of Exercise 0.0.5, valid at `d = 0` too). -/
theorem sauer_shelah {Ω : Type} [Fintype Ω] (F : Finset (Ω → Bool)) :
    (F.card : ℝ) ≤
        ∑ k ∈ Finset.range ((vcDim (F : Set (Ω → Bool))).toNat + 1),
          ((Fintype.card Ω).choose k : ℝ) ∧
      (F.card : ℝ) ≤
        (Real.exp 1 * (Fintype.card Ω : ℝ) / (vcDim (F : Set (Ω → Bool))).toNat) ^
          (vcDim (F : Set (Ω → Bool))).toNat := by sorry

end HighDimProb.Chaining
