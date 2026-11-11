-- Prove2me | Theorems.Thm_NMAffExt_LBP_theorem_1_6
-- name    : NMAffExt.LBP.theorem_1_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:30:01.279239+00:00
-- url     : https://prove2.me/theorems/509a62ad-9f8c-4621-acd2-b1c32bc6fea2
-- title:
--   Theorem 1.6 — affine non-malleability implies average-case hardness for weakly read-once linear branching programs, with and without auxiliary uniform bits
-- statement:
--   Let $1\le k<n$ and let $F:\mathbb F_2^n\to\mathbb F_2^m$ be $(k,\varepsilon)$ non-malleable against globally fixed-point-free affine involutions: for every affine source $X$ of dimension at least $k$ and every affine $T:\mathbb F_2^n\to\mathbb F_2^n$ with $T(T(x))=x$ and $T(x)\ne x$ for all $x$, $(F(X),F(T(X)))$ is within statistical distance $\varepsilon$ of $(U_m,F(T(X)))$. Every $(k,\varepsilon)$ non-malleable affine extractor has this property. Let $u\in\mathbb F_2^m\setminus\{0\}$.
--
--   1. Every weakly read-once linear branching program $P$ on $n$ bits with $s$ vertices satisfies
--   $$\Bigl|\mathbb E_{x\sim U_n}(-1)^{\langle u,F(x)\rangle+P(x)}\Bigr|\le\sqrt{2s\bigl(2\varepsilon+2^{-(n-k)}\bigr)}.$$
--   2. If moreover $k\le n-2$ and $\varepsilon\le 1/2$, then for every $t\ge0$ and every weakly read-once linear branching program $P$ on $(X,R)\in\mathbb F_2^n\times\mathbb F_2^t$ with $s$ vertices, with $X\sim U_n$ and $R\sim U_t$ independent,
--   $$\Bigl|\mathbb E_{X,R}(-1)^{\langle u,F(X)\rangle+P(X,R)}\Bigr|\le\sqrt{2s\bigl(2\varepsilon+(1-2\varepsilon)2^{-(n-k-1)}\bigr)}.$$
--
--   Here a linear branching program queries a linear form of the input at each internal node, its size counts all vertices, and it is weakly read-once when the form queried at each node lies outside the span of all forms queried on all source-to-node paths. With explicit non-malleable affine extractors of exponentially small error, the theorem gives exponential average-case lower bounds for this model, for which no hardness result for explicit functions was previously known.
--
--   Differences from the source:
--   - reading: "let F be a $(k,\varepsilon)$ non-malleable affine extractor … In both statements, non-malleability against globally fixed-point-free affine involutions suffices" → one theorem with hypothesis `IsNMAffExtInv k ε F`; reason: the theorem's last sentence; implied by `IsNMAffExt k ε F` (`IsNMAffExt.toInv`), so both readings of the hypothesis are covered.
--   - encoding: $k\le n-2$ → `k + 2 ≤ n`; reason: the same condition on natural numbers without truncated subtraction.
--   - encoding: a program on $(X,R)$ and $\mathbb E_{X,R}$ → a `Program (n + t) s` evaluated at `Fin.append x r`, averaged over all pairs $(x,r)$; reason: independent uniform $X,R$ is the uniform distribution on pairs.
-- source:
--   Xin Li, Yan Zhong, Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds, arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 6 (PDF 8), Theorem 1.6 (proved as Theorem 4.11, p. 59, and Theorem A.4, p. 103)

import Mathlib
import Definitions.Def_NMAffExt_LBP_Basic
import Definitions.Def_NMAffExt_LBP_NonMalleable
import Definitions.Def_NMAffExt_LBP_Program

namespace NMAffExt.LBP

/-- **Theorem 1.6.** Let `1 ≤ k < n` and let `F : 𝔽₂ⁿ → 𝔽₂ᵐ` be `(k, ε)` non-malleable against globally
fixed-point-free affine involutions (in particular, any `(k, ε)` non-malleable affine extractor).
For every `u ≠ 0`: (1) every size-`s` weakly read-once linear branching program `P` on `n` bits has
`|E_{x∼U_n} (−1)^{⟨u,F(x)⟩+P(x)}| ≤ √(2s(2ε + 2^{−(n−k)}))`; (2) if `k ≤ n − 2` and `ε ≤ 1/2`, then for
every `t ≥ 0` and every size-`s` weakly read-once linear branching program `P` on `(X, R)` (on
`n + t` bits), `|E_{X,R} (−1)^{⟨u,F(X)⟩+P(X,R)}| ≤ √(2s(2ε + (1 − 2ε)2^{−(n−k−1)}))`. -/
theorem theorem_1_6 (n m k : ℕ) (ε : ℝ) (F : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (hk : 1 ≤ k) (hkn : k < n) (hF : IsNMAffExtInv k ε F)
    (u : Fin m → ZMod 2) (hu : u ≠ 0) :
    (∀ (s : ℕ) (P : Program n s), P.IsWeaklyReadOnce →
      |avg (fun x : Fin n → ZMod 2 => sgn (ip u (F x) + P.eval x))| ≤
        Real.sqrt (2 * s * (2 * ε + (2 : ℝ) ^ (-((n : ℤ) - k))))) ∧
    (k + 2 ≤ n → ε ≤ 1 / 2 → ∀ (t s : ℕ) (P : Program (n + t) s), P.IsWeaklyReadOnce →
      |avg (fun xr : (Fin n → ZMod 2) × (Fin t → ZMod 2) =>
          sgn (ip u (F xr.1) + P.eval (Fin.append xr.1 xr.2)))| ≤
        Real.sqrt (2 * s * (2 * ε + (1 - 2 * ε) * (2 : ℝ) ^ (-((n : ℤ) - k - 1))))) := by sorry

end NMAffExt.LBP
