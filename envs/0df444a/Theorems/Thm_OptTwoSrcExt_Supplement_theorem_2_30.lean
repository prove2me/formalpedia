-- Prove2me | Theorems.Thm_OptTwoSrcExt_Supplement_theorem_2_30
-- name    : OptTwoSrcExt.Supplement.theorem_2_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:37:47.240103+00:00
-- url     : https://prove2.me/theorems/ea82701f-5d0f-4a1d-9a72-1f9e544b1fa1
-- title:
--   Theorem 2.30 — uniform positive affine regularization
-- statement:
--   Let $F:\mathbb F_2^n\times\mathbb F_2^n\to\mathbb F_2^D$ and suppose fixed maps $u_L,u_R:\mathbb F_2^n\to\mathbb F_2^P$ represent every character of $F$ by a bilinear form: for every $\lambda\in\mathbb F_2^D$ there is a $P\times P$ matrix $M_\lambda$ over $\mathbb F_2$ with
--   $$\lambda\cdot F(x,y)=u_L(x)^{\mathsf T}M_\lambda\,u_R(y)\qquad\text{for all }x,y,\tag{2.15}$$
--   the same $u_L,u_R$ for all $\lambda$.
--
--   There is an absolute constant $C_0$ such that the following holds. Let $X$ be uniform on a nonempty set $A_0\subseteq\mathbb F_2^n$ and $Y$ uniform on a nonempty set $B_0\subseteq\mathbb F_2^n$, independent, and let $r_*,u$ be integers with $1\le r_*\le P$, $u\ge1$, and $H\ge0$, $t\ge1$ reals. Then there is a finite partition of $A_0\times B_0$ into product rectangles $A'\times B'$ such that
--
--   1. on every leaf, the law of $F(X,Y)$ given $(X,Y)\in A'\times B'$ is within statistical distance $2^{D/2-H-1}$ of the uniform law on the affine hull of $F(A'\times B')$;
--   2. outside leaves of total mass at most $2^{1-t}$, each source loses at most
--   $$L=C_0\Big[\frac Pu+\frac P{r_*}\big(2u(H+1)+(u+1)\log(n+P+2)\big)+D(r_*+2)+t\Big]\tag{2.16}$$
--   bits of min-entropy, i.e. $\log(|A_0|/|A'|)\le L$ and $\log(|B_0|/|B'|)\le L$.
--
--   This shared-feature regularization reduces a bilinear-feature output on product sources to near-uniform affine pieces at a controlled entropy cost; it is the common engine of the paper's conversions.
--
--   **Formalization Note** $C_0$ is chosen before $n,D,P$, the maps and the sources. Logarithms are base 2. The partition is only asserted to exist. "The comparison is a positive mixture of uniform affine laws" describes the mixture of the leaves' uniform hull laws and needs no separate clause.
--
--   Differences from the source:
--   - reading: independent flat inputs (Definition 2.7: a flat k-source is uniform on exactly 2^k points) → X uniform on any nonempty finite A₀ ⊆ 𝔽₂ⁿ, Y uniform on any nonempty finite B₀ ⊆ 𝔽₂ⁿ, independent; reason: the paper also calls uniform laws on arbitrary subsets flat (Lemma 2.29 "flat sources on subsets of F_2^n", Lemma 5.3 "conditioning flat sources on a product rectangle preserves flatness"); the stronger reading, which contains the 2^k-point case, is taken
--   - encoding: "on every leaf the conditional output is within η of uniform on its exact affine hull"; "outside total leaf mass at most 2^{1−t} each source loses at most L bits" → leafHullDist ≤ η on every leaf; the masses |A′||B′|/(|A₀||B₀|) of the leaves on which log₂(|A₀|/|A′|) > L or log₂(|B₀|/|B′|) > L sum to at most 2^{1−t}; reason: conditioned on a leaf, independent flat sources are uniform on A′ × B′ (Lemma 5.3); these are the paper's quantities
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), §2.9 and Theorem 2.30, pp.26–27 (PDF pp.28–29)

import Mathlib
import Definitions.Def_OptTwoSrcExt_fourier
import Definitions.Def_OptTwoSrcExt_Supplement_IsRectPartition

open Classical OptTwoSrcExt

namespace OptTwoSrcExt.Supplement

/-- **Theorem 2.30 (Uniform positive affine regularization).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), §2.9 and Theorem 2.30, printed pp.26–27 (PDF pp.28–29):
"Let F : F_2^n × F_2^n → F_2^D. Assume fixed maps uL, uR : F_2^n → F_2^P represent every character
by a bilinear form: λ · F(x, y) = uL(x)^T Mλ uR(y) (λ ∈ F_2^D). (2.15) … There is an absolute C0
such that the following holds. For independent flat inputs, integers 1 ⩽ r∗ ⩽ P, u ⩾ 1, and real
H ⩾ 0, t ⩾ 1, there is a finite partition into raw product rectangles. On every leaf, the
conditional output is within 2^{D/2−H−1} of uniform on its exact affine hull. Outside total leaf
mass at most 2^{1−t}, each source loses at most
L = C0[P/u + (P/r∗)(2u(H + 1) + (u + 1) log(n + P + 2)) + D(r∗ + 2) + t] (2.16)
bits of min-entropy."

There is `C₀` such that for all `n, D, P`, every `F : 𝔽₂ⁿ × 𝔽₂ⁿ → 𝔽₂^D` and `u_L, u_R : 𝔽₂ⁿ → 𝔽₂^P`
with (2.15) (for each `λ` a `P × P` matrix `M_λ`, the same `u_L, u_R` for all `λ`), all nonempty
`A₀, B₀ ⊆ 𝔽₂ⁿ` (`X` uniform on `A₀`, `Y` uniform on `B₀`, independent), integers `1 ≤ r∗ ≤ P`,
`u ≥ 1` and reals `H ≥ 0`, `t ≥ 1`, there is a finite partition of `A₀ × B₀` into product rectangles
`A' × B'` such that
1. on every leaf, the law of `F(X, Y)` given `(X, Y) ∈ A' × B'` is within `2^{D/2 − H − 1}` of the
   uniform law on the affine hull of `F(A' × B')`;
2. the leaves on which `log₂(|A₀|/|A'|) > L` or `log₂(|B₀|/|B'|) > L` have total mass
   `Σ |A'||B'|/(|A₀||B₀|) ≤ 2^{1−t}`, with `L` as in (2.16).

**Formalization Note.** `C₀` is chosen before every other quantity ("absolute"). Logarithms are base 2.
A flat source is uniform on a nonempty finite set; the statement allows sets of any size (the paper's
flat `k`-sources have `2^k` points). The partition is only asserted to exist ("proof-only and need
not be computed"). "The comparison is a positive mixture of uniform affine laws" describes the
mixture of the leaves' uniform hull laws and needs no separate clause. -/
theorem theorem_2_30 :
    ∃ C₀ : ℝ, ∀ (n D P : ℕ) (F : (Fin n → ZMod 2) → (Fin n → ZMod 2) → (Fin D → ZMod 2))
      (uL uR : (Fin n → ZMod 2) → (Fin P → ZMod 2)),
      (∀ l : Fin D → ZMod 2, ∃ M : Matrix (Fin P) (Fin P) (ZMod 2),
        ∀ x y, dotF2 l (F x y) = dotProduct (uL x) (M.mulVec (uR y))) →
      ∀ (A₀ B₀ : Finset (Fin n → ZMod 2)), A₀.Nonempty → B₀.Nonempty →
      ∀ (rs u : ℕ) (H t : ℝ), 1 ≤ rs → rs ≤ P → 1 ≤ u → 0 ≤ H → 1 ≤ t →
        ∃ (ι : Type) (_ : Fintype ι) (Al : ι → Finset (Fin n → ZMod 2))
          (Bl : ι → Finset (Fin n → ZMod 2)),
          IsRectPartition A₀ B₀ Al Bl ∧
          (∀ i, leafHullDist F (Al i) (Bl i) ≤ (2 : ℝ) ^ ((D : ℝ) / 2 - H - 1)) ∧
          ∑ i, (if LosesAtMost A₀ B₀ (Al i) (Bl i)
              (C₀ * ((P : ℝ) / u + ((P : ℝ) / rs) * (2 * u * (H + 1) +
                (u + 1) * Real.logb 2 (n + P + 2)) + D * (rs + 2) + t))
            then 0 else leafMass A₀ B₀ (Al i) (Bl i)) ≤ (2 : ℝ) ^ (1 - t) := by sorry

end OptTwoSrcExt.Supplement
