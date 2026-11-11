-- Prove2me | Theorems.Thm_OptTwoSrcExt_proposition_3_31
-- name    : OptTwoSrcExt.proposition_3_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:26:15.654317+00:00
-- url     : https://prove2.me/theorems/ae1d1a73-909d-45f0-aaa4-8f400076f046
-- title:
--   Proposition 3.31 — mixed restricted-rank bound for $\mathrm{Tr}(\lambda(x+y)^d+\mu(f(x)+y)^d)$
-- statement:
--   Fix $h\ge3$, $d=2^h-1$, $K=\mathbb F_{2^N}$ with $N>2h$, and $L=2^{h-2}$. For $\lambda\in K^\times$, $\mu\in K$ and $f:K\to K$, let
--   $$M(x,y)=\mathrm{Tr}_{K/\mathbb F_2}\big(\lambda(x+y)^d+\mu(f(x)+y)^d\big).$$
--   1. For finite $A,B\subseteq K$ with $f(x)\ne x$ on $A$, and an integer $p$ with $4p\le L$, $|A|\ge\max\{12,4p\}$ and $|B|\ge2(d-1)2^{N/2}$,
--   $$\mathrm{rank}_2\,M[A,B]\ \ge\ p\log|A|-p\log(4p)+\log|B|-N-1 .\tag{3.35}$$
--   2. The full-domain matrix $M[K,K]$, for any extension of $f$ to $K$, has $\mathrm{rank}_2\le2^{h+1}N$.
--
--   High rank on every large rectangle together with low global rank is what lets the dispersion upgrade (Corollary 2.20) turn this tampered character into an extractor.
--
--   **Formalization Note** $K$ is `GaloisField 2 N`, the trace is the absolute trace to $\mathbb F_2$, and $\mathrm{rank}_2$ is the binary rank of the $0/1$ table. The standing phrase "taking $N$ sufficiently large below" concerns Corollary 3.32 and is not a hypothesis here.
--
--   Differences from the source:
--   - encoding: fixed-point-free f : A → K; the full-domain matrix for any extension of f → f : K → K with f(x) ≠ x on A; clause 2 for the same arbitrary f : K → K; reason: every map K → K is an extension of its restriction to A, and every extension arises this way
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Proposition 3.31, p.47 (PDF p.49); standing assumptions of §3.2.11, p.46 (PDF p.48)

import Mathlib
import Definitions.Def_OptTwoSrcExt_rank2

namespace OptTwoSrcExt

/-- **Proposition 3.31 (Mixed restricted-rank bound).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Proposition 3.31, printed p.47 (PDF p.49), under the
standing assumptions of §3.2.11, printed p.46 (PDF p.48): "Fix h ⩾ 3, d = 2^h − 1, K = F_{2^N}, and
N > 2h, taking N sufficiently large below. Put L = 2^{h−2}." Statement: "For λ ∈ K×, µ ∈ K, and
fixed-point-free f : A → K, let M(x, y) = Tr_{K/F2}(λ(x + y)^d + µ(f(x) + y)^d). If 4p ⩽ L,
|A| ⩾ max{12, 4p}, and |B| ⩾ 2(d − 1)2^{N/2}, then
rank2 M[A, B] ⩾ p log |A| − p log(4p) + log |B| − N − 1. (3.35)
The full-domain matrix, for any extension of f, has rank at most 2^{h+1}N."

Let `h ≥ 3`, `N > 2h`, `K = 𝔽_{2^N}`, `d = 2^h − 1`, `L = 2^{h−2}`, `λ ≠ 0`, `μ ∈ K` and `f : K → K`, and
put `M(x, y) = Tr_{K/𝔽₂}(λ(x + y)^d + μ(f(x) + y)^d)`.
1. For finite `A, B ⊆ K` with `f(x) ≠ x` on `A`, and `p` with `4p ≤ L`, `|A| ≥ 12`, `|A| ≥ 4p`,
   `|B| ≥ 2(d − 1)2^{N/2}`: `rank₂ M[A, B] ≥ p log₂|A| − p log₂(4p) + log₂|B| − N − 1`.
2. The full matrix `M[K, K]` has `rank₂ ≤ 2^{h+1}N`.

**Formalization Note.** `K` is `GaloisField 2 N`, the trace is `Algebra.trace (ZMod 2) K`, and
`rank₂` is `OptTwoSrcExt.rank2` (rank over `𝔽₂` of the `0/1` table). `f : A → K` is a map `K → K`;
its values off `A` are an arbitrary extension, which is how clause 2 covers "any extension of f".
The standing "N sufficiently large" concerns Corollary 3.32 and is not a hypothesis here. -/
theorem proposition_3_31 (h N : ℕ) (hh : 3 ≤ h) (hN : 2 * h < N) (lam μ : GaloisField 2 N)
    (hlam : lam ≠ 0) (f : GaloisField 2 N → GaloisField 2 N) :
    (∀ (A B : Finset (GaloisField 2 N)) (p : ℕ), (∀ x ∈ A, f x ≠ x) → 4 * p ≤ 2 ^ (h - 2) →
      12 ≤ A.card → 4 * p ≤ A.card →
      2 * ((2 ^ h - 1 - 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((N : ℝ) / 2) ≤ B.card →
        (p : ℝ) * Real.logb 2 A.card - p * Real.logb 2 (4 * p) + Real.logb 2 B.card - N - 1 ≤
          (rank2 (fun (x : A) (y : B) =>
            Algebra.trace (ZMod 2) (GaloisField 2 N)
              (lam * ((x : GaloisField 2 N) + y) ^ (2 ^ h - 1) +
                μ * (f x + y) ^ (2 ^ h - 1))) : ℝ)) ∧
    (rank2 (fun x y : GaloisField 2 N =>
        Algebra.trace (ZMod 2) (GaloisField 2 N)
          (lam * (x + y) ^ (2 ^ h - 1) + μ * (f x + y) ^ (2 ^ h - 1))) : ℝ) ≤
      (2 : ℝ) ^ (h + 1) * N := by sorry

end OptTwoSrcExt
