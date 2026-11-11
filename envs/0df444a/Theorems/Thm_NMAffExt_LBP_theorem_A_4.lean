-- Prove2me | Theorems.Thm_NMAffExt_LBP_theorem_A_4
-- name    : NMAffExt.LBP.theorem_A_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:29:51.27934+00:00
-- url     : https://prove2.me/theorems/fd1da8b9-441c-4126-bdec-225d4d06ca2c
-- title:
--   Theorem A.4 — with independent uniform auxiliary bits $R\sim U_t$: correlation $\le\sqrt{2s(2\varepsilon+(1-2\varepsilon)2^{-(n-k-1)})}$
-- statement:
--   Let $F:\mathbb F_2^n\to\mathbb F_2^m$ be $(k,\varepsilon)$ non-malleable against globally fixed-point-free affine involutions (in particular, any $(k,\varepsilon)$ non-malleable affine extractor), where $1\le k\le n-2$ and $0\le\varepsilon\le 1/2$. Let $t\ge0$ and let $X\sim U_n$ and $R\sim U_t$ be independent. For every nonzero $u\in\mathbb F_2^m$ and every weakly read-once linear branching program $P$ on $(X,R)$ (on $n+t$ bits) with $s$ vertices,
--   $$\Bigl|\mathbb E_{X,R}(-1)^{\langle u,F(X)\rangle+P(X,R)}\Bigr|\le\sqrt{2s\bigl(2\varepsilon+(1-2\varepsilon)2^{-(n-k-1)}\bigr)}.\qquad\text{(A.5)}$$
--   The bound does not depend on $t$.
--
--   Differences from the source:
--   - reading: "Let F be a $(k,\varepsilon)$ non-malleable affine extractor … Non-malleability against globally fixed-point-free affine involutions suffices" → hypothesis `IsNMAffExtInv k ε F`; reason: the theorem's last sentence; implied by `IsNMAffExt k ε F`, so both sentences are covered.
--   - encoding: $k\le n-2$ → `k + 2 ≤ n`; reason: the same condition on natural numbers without truncated subtraction.
--   - encoding: a program on $(X,R)$ and $\mathbb E_{X,R}$ → a `Program (n + t) s` evaluated at `Fin.append x r`, averaged over all pairs $(x,r)$; reason: independent uniform $X,R$ is the uniform distribution on pairs.
-- source:
--   Xin Li, Yan Zhong, Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds, arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 103 (PDF 105), Theorem A.4, eq. (A.5)

import Mathlib
import Definitions.Def_NMAffExt_LBP_Basic
import Definitions.Def_NMAffExt_LBP_NonMalleable
import Definitions.Def_NMAffExt_LBP_Program

namespace NMAffExt.LBP

/-- **Theorem A.4.** Let `F` be `(k, ε)` non-malleable against globally fixed-point-free affine
involutions, `1 ≤ k ≤ n − 2`, `0 ≤ ε ≤ 1/2`, and let `X ∼ U_n`, `R ∼ U_t` be independent. For every
nonzero `u` and every size-`s` weakly read-once linear branching program `P` on `(X, R)` (on `n + t`
bits), `|E_{X,R} (−1)^{⟨u,F(X)⟩ + P(X,R)}| ≤ √(2s(2ε + (1 − 2ε)2^{−(n−k−1)}))`, for every `t`. -/
theorem theorem_A_4 (n m k : ℕ) (ε : ℝ) (F : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (hF : IsNMAffExtInv k ε F) (hk : 1 ≤ k) (hkn : k + 2 ≤ n) (hε₀ : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (t : ℕ) (u : Fin m → ZMod 2) (hu : u ≠ 0) (s : ℕ) (P : Program (n + t) s)
    (hP : P.IsWeaklyReadOnce) :
    |avg (fun xr : (Fin n → ZMod 2) × (Fin t → ZMod 2) =>
        sgn (ip u (F xr.1) + P.eval (Fin.append xr.1 xr.2)))| ≤
      Real.sqrt (2 * s * (2 * ε + (1 - 2 * ε) * (2 : ℝ) ^ (-((n : ℤ) - k - 1)))) := by sorry

end NMAffExt.LBP
