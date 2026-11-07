-- Prove2me | Theorems.Thm_LowErrExt_lemma_5_3
-- name    : LowErrExt.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:49.346651+00:00
-- url     : https://prove2.me/theorems/7587adbf-9634-426f-b73f-de7da93cb850
-- title:
--   Lemma 5.3 — a new recipe for two-source extractors
-- statement:
--   There is a universal constant $C\ge1$ such that the following holds. Suppose
--
--   1. $\mathrm{swCond}:\mathbb F_2^n\times[D]\to\mathbb F_2^{n_1}$ is a $k_0\to k_1$ somewhere rank condenser;
--   2. $\mathrm{Ext}':\mathbb F_2^{n_1}\times\mathbb F_2^{n_1}\to\mathbb F_2^{n_2}$ is bilinear and a $k_1$-two-source rank extractor;
--   3. $\mathrm{SUExt}:(\mathbb F_2^{n_2})^{D^2}\to\mathbb F_2^m$ is an extractor for somewhere-uniform affine sources with error $\delta$.
--
--   Then $\mathrm{Ext}(x,y):=\mathrm{SUExt}\big((\mathrm{Ext}'(\mathrm{swCond}(x,i),\mathrm{swCond}(y,j)))_{i,j\in[D]}\big)$ is a two-source extractor for every min-entropy
--   $$k\ge k_0+2C\big(D^{4C+4}n_1^{2C}n_2^{C+2}\big)^{1/(2C+1)}+3Cn_2D^2$$
--   with error $\varepsilon=\delta+4\cdot2^{-n_2D^2}$.
--
--   Differences from the source:
--   - encoding: (𝔽₂^{n₂})^{D²} with rows (i, j) ∈ [D]² → rows indexed by Fin D × Fin D; reason: same index set
--   - encoding: an extractor for SU affine sources with error δ → SUExt(Z) is within statistical distance δ of uniform on 𝔽₂^m for every SU-affine Z; reason: the standard meaning; Definition 3.31 defines the sources
--   - encoding: for min-entropy k ≥ bound → for every real k at least the bound; reason: same statement
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Lemma 5.3, p.34

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_IsAffineSource
import Definitions.Def_LowErrExt_IsSeededRankCond
import Definitions.Def_LowErrExt_IsTwoSourceRankExt
import Definitions.Def_LowErrExt_IsTwoSourceExtractor

open FuzzyExtractors.Hamming

namespace LowErrExt

/-- **Lemma 5.3 (A new recipe for two-source extractors).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Lemma 5.3, p.34: "Suppose you have the following objects. • A somewhere rank condenser: A function
swCond : Fn2 × [D] → Fn12 that is a k0 → k1 somewhere rank condenser, as defined by Definition 3.2.
• A bilinear two-source rank extractor: A bilinear function Ext′ : Fn12 × Fn12 → Fn22 that is a
k1-two-source rank extractor, as defined by Definition 3.21. • An extractor for somewhere-uniform affine
sources: A function SUExt : (Fn22)^{D²} → Fm2 that is an extractor for somewhere-uniform affine sources
with error δ, as defined by Definition 3.31. Then, the function Ext : Fn2 × Fn2 → Fm2 defined as
Ext(x, y) := SUExt((Ext′(swCond(x, i), swCond(y, j)))_{i,j∈[D]}) is a two-source extractor for
min-entropy k ≥ k0 + 2C(D^{4C+4}n1^{2C}n2^{C+2})^{1/(2C+1)} + 3Cn2D² with error ε = δ + 4 · 2^{−n2D²},
for some universal constant C ≥ 1."

**Formalization Note.** `C` is chosen before every parameter. The `D²` rows are indexed by
`[D] × [D]`. `swCond` is not assumed linear (the page does not assume it). "Extractor for SU affine
sources with error `δ`": every SU-affine source `Z` has `SUExt(Z)` within statistical distance `δ` of
uniform on `𝔽₂ᵐ`. "For min-entropy `k ≥ …`" is read as: for every `k` at least the bound. -/
theorem lemma_5_3 :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (n D n₁ n₂ m : ℕ) (k₀ k₁ δ : ℝ)
        (swCond : (Fin n → ZMod 2) → Fin D → (Fin n₁ → ZMod 2))
        (Ext' : (Fin n₁ → ZMod 2) → (Fin n₁ → ZMod 2) → (Fin n₂ → ZMod 2))
        (SUExt : (Fin D × Fin D → Fin n₂ → ZMod 2) → (Fin m → ZMod 2)),
        IsSomewhereRankCond k₀ k₁ swCond → IsBilinear Ext' → IsTwoSourceRankExt k₁ Ext' →
        (∀ Z : PMF (Fin D × Fin D → Fin n₂ → ZMod 2), IsSUAffine Z →
            statDist (Z.map SUExt) (PMF.uniformOfFintype (Fin m → ZMod 2)) ≤ δ) →
        ∀ k : ℝ,
          k₀ + 2 * C * ((D : ℝ) ^ (4 * C + 4) * (n₁ : ℝ) ^ (2 * C) * (n₂ : ℝ) ^ (C + 2)) ^ (1 / (2 * C + 1)) +
              3 * C * n₂ * (D : ℝ) ^ 2 ≤ k →
            IsTwoSourceExtractor k (δ + 4 * (2 : ℝ) ^ (-((n₂ : ℝ) * (D : ℝ) ^ 2)))
              (fun x y : Fin n → ZMod 2 => SUExt fun ij => Ext' (swCond x ij.1) (swCond y ij.2)) := by sorry

end LowErrExt
