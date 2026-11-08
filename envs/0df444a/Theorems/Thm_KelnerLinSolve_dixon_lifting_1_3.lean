-- Prove2me | Theorems.Thm_KelnerLinSolve_dixon_lifting_1_3
-- name    : KelnerLinSolve.dixon_lifting_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:55:18.367201+00:00
-- url     : https://prove2.me/theorems/d8b9948b-91ed-45e2-a816-843b95b2083f
-- title:
--   §2.1, (1)–(3) — Dixon's lifting: exact division and the invariant $My_k \equiv b \pmod{R^k}$
-- statement:
--   Let $R \ge 2$ be an integer and let $M, C \in \mathbb Z^{n\times n}$ satisfy $MC \equiv I \pmod R$ entrywise. For $b \in \mathbb Z^n$ run Dixon's lifting: $b_0 = b$,
--
--   $$
--   x_i = C b_i \bmod R, \qquad b_{i+1} = \frac{b_i - M x_i}{R}, \qquad y_k = \sum_{i=0}^{k-1} R^i x_i .
--   $$
--
--   Then for all $i, k \ge 0$:
--
--   1. every coordinate of $x_i$ lies in $\{0,\dots,R-1\}$;
--   2. the division is exact: $R\,b_{i+1} = b_i - M x_i$;
--   3. $M y_k = b - R^k b_k$;
--   4. $M y_k \equiv b \pmod{R^k}$, which is (1).
--
--   This is Step 2 of Dixon's algorithm, the base of the exact solver.
--
--   Differences from the source:
--   - generalization: C from Step 1 has entries in {0, …, R − 1} → any integer matrix C with MC ≡ I (mod R); reason: the argument never uses the range of C; the statement specializes to Step 1's C
--   - encoding: M invertible with gcd(R, det M) = 1 → not stated as hypotheses; reason: both follow from MC ≡ I (mod R) with R ≥ 2 (det M · det C ≡ 1), so the instances are the same
--   - encoding: x_i := C b_i mod R, (b_i − M x_i)/R → `Int.emod`, `Int.ediv`; exactness of the division is a conclusion; reason: Lean convention; same values on the page's instances
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), §2.1, Step 2, p.4, Equations (1)–(3)

import Mathlib
import Definitions.Def_KelnerLinSolve_dixonRes

open Matrix

namespace KelnerLinSolve

/-- **Dixon's lifting, invariant (1) and recurrence (2)–(3)**, Kelner, *Solving Linear Systems in
Õ(mn log(κ/ε)) Bit Operations*, STOC 2027 submission (sha256 d1af55cb…), §2.1, Step 2, p.4. "We
iteratively construct a sequence of vectors `{xᵢ}_{i=0}^{L−1}` with entries in `{0, …, R − 1}` such
that the sums `y_k := ∑_{i=0}^{k−1} Rⁱxᵢ` obey `M y_k ≡ b (mod R^k)`, (1) … we initialize `b₀ := b`
and compute … `xᵢ := C bᵢ mod R` (2) `b_{i+1} := (bᵢ − M xᵢ)/R`. (3)"

For integers `R ≥ 2` and integer matrices `M, C` with `M C ≡ I (mod R)` (Step 1), the digits lie
in `{0, …, R − 1}`, the division in (3) is exact (`R b_{i+1} = bᵢ − M xᵢ`), `M y_k = b − R^k b_k`,
and hence (1) holds for every `k`.

**Formalization Note.** `dixonRes` computes (3) with `Int.ediv`, so exactness is part of the
conclusion. The entries of `C` are not required to lie in `{0, …, R − 1}`. -/
theorem dixon_lifting_1_3 {n : ℕ} (M C : Matrix (Fin n) (Fin n) ℤ) (R : ℤ) (b : Fin n → ℤ)
    (hR : 2 ≤ R) (hMC : ∀ i j, R ∣ (M * C - 1) i j) :
    (∀ (i : ℕ) (r : Fin n), 0 ≤ dixonDigit M C R b i r ∧ dixonDigit M C R b i r < R) ∧
    (∀ i : ℕ, R • dixonRes M C R b (i + 1) = dixonRes M C R b i - M *ᵥ dixonDigit M C R b i) ∧
    (∀ k : ℕ, M *ᵥ dixonPrefix M C R b k = b - R ^ k • dixonRes M C R b k) ∧
    (∀ (k : ℕ) (r : Fin n), R ^ k ∣ (M *ᵥ dixonPrefix M C R b k) r - b r) := by sorry

end KelnerLinSolve
