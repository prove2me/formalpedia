-- Prove2me | Theorems.Thm_OptTwoSrcExt_Supplement_theorem_5_5
-- name    : OptTwoSrcExt.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:42:41.174943+00:00
-- url     : https://prove2.me/theorems/d2563471-ace9-469c-b8db-befb5f260a8e
-- title:
--   Theorem 5.5 — feature regularization for $F=B(\phi(x),\psi(y))$
-- statement:
--   Let $\phi:\mathbb F_2^n\to\mathbb F_2^{p_L}$ and $\psi:\mathbb F_2^n\to\mathbb F_2^{p_R}$ be fixed maps (possibly nonlinear or noninjective), put $P=p_L+p_R$, and let $F(x,y)=B(\phi(x),\psi(y))\in\mathbb F_2^D$ for a fixed $\mathbb F_2$-bilinear map $B$.
--
--   There is an absolute constant $K_0$ such that the following holds. Let $X$ be uniform on a nonempty set $A_0\subseteq\mathbb F_2^n$ and $Y$ uniform on a nonempty set $B_0\subseteq\mathbb F_2^n$, independent, let $R,u\ge1$ be integers and $v\ge0$, $z\ge1$. Then there is a finite deterministic product-rectangle partition of $A_0\times B_0$ such that
--
--   1. on every leaf $\tau$, the output law is within statistical distance $2^{D/2-v-1}$ of uniform on its output affine hull;
--   2. except on leaves of total mass at most $2^{1-z}$, each input loses at most
--   $$L=K_0\Big[\frac Pu+\frac PR\big(2u(v+1)+(u+1)\log(n+P+2)\big)+D(R+2)+z\Big]\tag{5.1}$$
--   bits of min-entropy.
--
--   The partition is used only in the proof and is not computed by the extractor. This is the normalization of the regularization theorem used in the low-entropy construction of Section 5.
--
--   **Formalization Note** $K_0$ is chosen before every other quantity. Logarithms are base 2. There is no condition $R\le P$.
--
--   Differences from the source:
--   - reading: independent flat sources (Definition 2.7: a flat k-source is uniform on exactly 2^k points) → X uniform on any nonempty finite A₀ ⊆ 𝔽₂ⁿ, Y uniform on any nonempty finite B₀ ⊆ 𝔽₂ⁿ, independent; reason: the paper also calls uniform laws on arbitrary subsets flat (Lemma 2.29; Lemma 5.3 "conditioning independent flat sources on a product rectangle preserves their independence and flatness"); the stronger reading, which contains the 2^k-point case, is taken
--   - encoding: "on every leaf the output law is within η of uniform on its output affine hull"; "except on leaves of total mass at most 2^{1−z} each input loses at most L bits" → leafHullDist ≤ η on every leaf; the masses |A′||B′|/(|A₀||B₀|) of the leaves on which log₂(|A₀|/|A′|) > L or log₂(|B₀|/|B′|) > L sum to at most 2^{1−z}; reason: conditioned on a leaf, independent flat sources are uniform on A′ × B′ (Lemma 5.3); these are the paper's quantities
--   - reading: "integers R, u ⩾ 1, and v ⩾ 0, z ⩾ 1" → R, u natural numbers ≥ 1; v ≥ 0 and z ≥ 1 real; reason: the sentence leaves the type of v, z open; the real reading contains the integer one (Theorem 2.30 takes the corresponding H, t real)
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), §5.1.3 and Theorem 5.5, p.103 (PDF p.105)

import Mathlib
import Definitions.Def_OptTwoSrcExt_Supplement_IsRectPartition

open Classical OptTwoSrcExt

namespace OptTwoSrcExt.Supplement

/-- **Theorem 5.5 (Feature regularization).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), §5.1.3 and Theorem 5.5, printed p.103 (PDF p.105):
"Let ϕ : F_2^n → F_2^{pL} and ψ : F_2^n → F_2^{pR} be fixed maps, put P = pL + pR, and let
F(x, y) = B(ϕ(x), ψ(y)) ∈ F_2^D for a fixed bilinear map B. … There is an absolute constant K0 such
that the following holds. For independent flat sources X, Y, integers R, u ⩾ 1, and v ⩾ 0, z ⩾ 1,
there is a finite deterministic product-rectangle partition with these properties. (i) On every leaf
τ, the output law is within 2^{D/2−v−1} of uniform on its output affine hull. (ii) Except on leaves
of total mass at most 2^{1−z}, each input loses at most
L = K0[P/u + (P/R)(2u(v + 1) + (u + 1) log(n + P + 2)) + D(R + 2) + z] (5.1)
bits of min-entropy."

There is `K₀` such that for all `n, p_L, p_R, D`, all maps `ϕ : 𝔽₂ⁿ → 𝔽₂^{p_L}`,
`ψ : 𝔽₂ⁿ → 𝔽₂^{p_R}` (arbitrary), every `𝔽₂`-bilinear `B : 𝔽₂^{p_L} × 𝔽₂^{p_R} → 𝔽₂^D`, with
`F(x, y) = B(ϕ(x), ψ(y))` and `P = p_L + p_R`, all nonempty `A₀, B₀ ⊆ 𝔽₂ⁿ` (`X`, `Y` independent and
uniform on them), integers `R, u ≥ 1` and reals `v ≥ 0`, `z ≥ 1`, there is a finite partition of
`A₀ × B₀` into product rectangles `A' × B'` such that
1. on every leaf the law of `F(X, Y)` given the leaf is within `2^{D/2 − v − 1}` of uniform on the
   affine hull of `F(A' × B')`;
2. the leaves on which `log₂(|A₀|/|A'|) > L` or `log₂(|B₀|/|B'|) > L` have total mass at most
   `2^{1−z}`, with `L` as in (5.1).

**Formalization Note.** `K₀` is chosen before every other quantity. Logarithms are base 2. A flat
source is uniform on a nonempty finite set of any size. `v` and `z` are real. There is no condition
`R ≤ P`. The partition is only asserted to exist. -/
theorem theorem_5_5 :
    ∃ K₀ : ℝ, ∀ (n pL pR D : ℕ) (ϕ : (Fin n → ZMod 2) → (Fin pL → ZMod 2))
      (ψ : (Fin n → ZMod 2) → (Fin pR → ZMod 2))
      (B : (Fin pL → ZMod 2) →ₗ[ZMod 2] (Fin pR → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2))
      (A₀ B₀ : Finset (Fin n → ZMod 2)), A₀.Nonempty → B₀.Nonempty →
      ∀ (R u : ℕ) (v z : ℝ), 1 ≤ R → 1 ≤ u → 0 ≤ v → 1 ≤ z →
        ∃ (ι : Type) (_ : Fintype ι) (Al : ι → Finset (Fin n → ZMod 2))
          (Bl : ι → Finset (Fin n → ZMod 2)),
          IsRectPartition A₀ B₀ Al Bl ∧
          (∀ i, leafHullDist (fun x y => B (ϕ x) (ψ y)) (Al i) (Bl i) ≤
            (2 : ℝ) ^ ((D : ℝ) / 2 - v - 1)) ∧
          ∑ i, (if LosesAtMost A₀ B₀ (Al i) (Bl i)
              (K₀ * (((pL + pR : ℕ) : ℝ) / u + (((pL + pR : ℕ) : ℝ) / R) * (2 * u * (v + 1) +
                (u + 1) * Real.logb 2 (n + (pL + pR : ℕ) + 2)) + D * (R + 2) + z))
            then 0 else leafMass A₀ B₀ (Al i) (Bl i)) ≤ (2 : ℝ) ^ (1 - z) := by sorry

end OptTwoSrcExt.Supplement
