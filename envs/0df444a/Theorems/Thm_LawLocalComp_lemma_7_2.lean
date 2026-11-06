-- Prove2me | Theorems.Thm_LawLocalComp_lemma_7_2
-- name    : LawLocalComp.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:15:40.055195+00:00
-- url     : https://prove2.me/theorems/1dfb0f2c-4a82-4e21-be59-35128e78be2b
-- title:
--   Lemma 7.2 (Tail transfer with two budgets)
-- statement:
--   Fix an integer $r\ge1$, $0<\delta<1$ and $\rho>1$. Let $T$ partition each residual $R$ of $X=b+R$ into $\{0\}$, $(0,\delta\nu)$, ratio-$\rho$ intervals in $[\delta\nu,3\nu r)$ and the tail cell $[3\nu r,\infty)$, replace the full value $b+R$ by its cell mean, and fix point masses. For $n$ independent lattice-log-concave jobs with nonnegative directions of rank $q$ and any monotone norm $g$, with $F=\mathbb E g(L)$ and $\tilde F$ the value for the replaced laws,
--   $$\big[1-\min\{n2^{-r},\,6q(r+2)2^{-r}\}\big]F\le(\rho+\delta)\tilde F,\qquad\tilde F\le F.\tag{31}$$
--   In particular this holds for at most $N$ jobs of rank at most $q$ with $N$ in place of $n$, and without a rank promise the $n2^{-r}$ term alone is valid.
--
--   Differences from the source:
--   - generalization: at most N jobs with direction rank at most q → exactly n jobs, with q the direction rank of the selection; reason: the bound is monotone in n and q, so it implies the printed form and its rank-free sentence
--   - reading: ratio-ρ intervals in [δν, 3νr) → the intervals [δνρ^i, min{δνρ^{i+1}, 3νr}) for i ≥ 0; reason: the natural anchoring at δν
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 7.2, (31), p.13

import Mathlib
import Definitions.Def_LawLocalComp_tailMap
import Definitions.Def_LawLocalComp_IsLatticeLC
import Definitions.Def_LawLocalComp_IsMonotoneNorm
import Definitions.Def_LawLocalComp_expNorm
import Definitions.Def_LawLocalComp_dirRank

namespace LawLocalComp

/-- **Lemma 7.2 (Tail transfer with two budgets).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 7.2, (31), p.13.

Fix an integer `r ≥ 1`, `0 < δ < 1` and `ρ > 1`, and let `tailMap r δ ρ` partition each residual into
`{0}`, `(0, δν)`, ratio-`ρ` intervals in `[δν, 3νr)` and the tail cell `[3νr, ∞)`, replace the full
value `b + R` by its cell mean and fix point masses. For `n` independent lattice-log-concave jobs with
nonnegative directions of rank `q` and any monotone norm `g`,
`[1 − min{n2^{−r}, 6q(r + 2)2^{−r}}]F ≤ (ρ + δ)F̃` and `F̃ ≤ F`.

**Formalization Note.** Stated with the exact job count `n` and rank `q = dim span{a_j}`; this implies
the printed form for at most `N` jobs of rank at most `q`, and its rank-free sentence (the `n2^{−r}`
term alone). -/
theorem lemma_7_2 (r : ℕ) (hr : 1 ≤ r) (δ ρ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hρ : 1 < ρ)
    {d n : ℕ} (X : Fin n → Law) (hX : ∀ j, IsLatticeLC (X j)) (a : Fin n → Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j) (g : (Fin d → ℝ) → ℝ) (hg : IsMonotoneNorm g) :
    (1 - min ((n : ℝ) * (2 : ℝ)⁻¹ ^ r) (6 * (dirRank a : ℝ) * (r + 2) * (2 : ℝ)⁻¹ ^ r)) *
        expNorm g X a ≤ (ρ + δ) * expNorm g (fun j => tailMap r δ ρ (X j)) a ∧
      expNorm g (fun j => tailMap r δ ρ (X j)) a ≤ expNorm g X a := by sorry

end LawLocalComp
