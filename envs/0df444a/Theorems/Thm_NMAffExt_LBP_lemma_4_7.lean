-- Prove2me | Theorems.Thm_NMAffExt_LBP_lemma_4_7
-- name    : NMAffExt.LBP.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:29:43.331967+00:00
-- url     : https://prove2.me/theorems/e637462c-4bbd-45c3-9eff-2b49a10d1109
-- title:
--   Lemma 4.7 — affine sections $\sigma_b$ from future transcripts at a cut node
-- statement:
--   Let $P$ be a full weakly read-once linear branching program on $n$ bits, $1\le k<n$, and let $v$ be a node such that every path from the source to $v$ has the same $k$-dimensional query span $W$ (as every node of the cut of Lemma 4.6 does). Let the rows of $Q\in\mathbb F_2^{k\times n}$ form a basis of $W$ and put $d=n-k$. Then there are maps $\sigma_b:\mathbb F_2^k\to\mathbb F_2^n$, $b\in\mathbb F_2^d$, such that:
--
--   1. each $\sigma_b$ is affine and $Q\sigma_b=\mathrm{id}$; the images of $\sigma_b$ for distinct $b$ are disjoint, and together they cover $\mathbb F_2^n$;
--   2. the map $(a,b)\mapsto\sigma_b(a)$ is a bijection $\mathbb F_2^k\times\mathbb F_2^d\to\mathbb F_2^n$ (so a uniform input corresponds to independent uniform $a,b$);
--   3. there is $P_v:\mathbb F_2^d\to\mathbb F_2$ such that the subprogram started at $v$ outputs $P_v(b)$ on $\sigma_b(a)$ for every $a,b$; and on every input $x$ whose computation reaches $v$, the subprogram started at $v$ outputs $P(x)$.
--
--   Differences from the source:
--   - generalization: "Fix a node $v$ in the cut of Lemma 4.6, let $Q=Q_v$" → any node $v$ of any full weakly read-once program all of whose source paths have the same $k$-dimensional query span $W$, and any $Q$ whose rows are a basis of $W$; reason: every cut node of Lemma 4.6 has this property (its item 2), so the Lean statement specializes to the source's.
--   - encoding: "uniform input corresponds to independent uniform $a,b$" → bijectivity of $(a,b)\mapsto\sigma_b(a)$; reason: the source derives the first from the second ("so").
-- source:
--   Xin Li, Yan Zhong, Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds, arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), pp. 57–58 (PDF 59–60), Lemma 4.7

import Mathlib
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_NMAffExt_LBP_Program

open Matrix

namespace NMAffExt.LBP

/-- **Lemma 4.7.** Let `P` be a full weakly read-once linear branching program on `n` bits,
`1 ≤ k < n`, and `v` a node every path to which has the same `k`-dimensional query span `W` (the
property of the cut nodes of Lemma 4.6); let the rows of `Q` form a basis of `W` and `d = n − k`.
There are affine maps `σ_b : 𝔽₂ᵏ → 𝔽₂ⁿ` (`b ∈ 𝔽₂ᵈ`) with (1) `Q σ_b = id` for every `b`, the images
pairwise disjoint and covering `𝔽₂ⁿ`; (2) `(a, b) ↦ σ_b(a)` a bijection; (3) a Boolean
`P_v : 𝔽₂ᵈ → 𝔽₂` with the subprogram started at `v` outputting `P_v(b)` on `σ_b(a)` for every `a, b`,
and this output equals `P(x)` on inputs `x` reaching `v`. -/
theorem lemma_4_7 (n k s : ℕ) (P : Program n s) (hP : P.IsWeaklyReadOnce) (hfull : P.IsFull)
    (hk : 1 ≤ k) (hkn : k < n) (v : Fin s) (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hW : Module.finrank (ZMod 2) W = k) (hpath : ∀ l, P.IsPathTo l v → P.pathSpan l = W)
    (Q : Matrix (Fin k) (Fin n) (ZMod 2)) (hQ : RowsBasis Q W) :
    ∃ σ : (Fin (n - k) → ZMod 2) → (Fin k → ZMod 2) → (Fin n → ZMod 2),
      (∀ b, QuadExt.Main.IsAffineMap (σ b) ∧ ∀ a, Q *ᵥ σ b a = a) ∧
      (∀ b b', b ≠ b' → Disjoint (Set.range (σ b)) (Set.range (σ b'))) ∧
      (∀ x, ∃ b a, σ b a = x) ∧
      Function.Bijective (fun p : (Fin k → ZMod 2) × (Fin (n - k) → ZMod 2) => σ p.2 p.1) ∧
      ∃ Pv : (Fin (n - k) → ZMod 2) → ZMod 2,
        (∀ a b, P.evalFrom v (σ b a) = Pv b) ∧
        (∀ x, P.Reaches x v → P.evalFrom v x = P.eval x) := by sorry

end NMAffExt.LBP
