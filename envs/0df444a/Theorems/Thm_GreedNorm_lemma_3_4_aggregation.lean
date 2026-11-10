-- Prove2me | Theorems.Thm_GreedNorm_lemma_3_4_aggregation
-- name    : GreedNorm.lemma_3_4_aggregation
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:35.057411+00:00
-- url     : https://prove2.me/theorems/c39e0ae4-649a-4d43-877a-94d12455fedc
-- title:
--   Proof of Lemma 3.4, Step 2 — aggregating a cover costs at most the sum of its costs (corrected: nonempty cover)
-- statement:
--   Let $\mathrm{load}_i:2^U\to\mathbb R_{\ge0}$ be monotone and subadditive, $g$ a monotone symmetric norm on $\mathbb R^m$, $C$ a nonempty finite family of partial assignments, and $\sigma:U\to[m]$ an assignment such that for every element $e$ some $\hat\sigma\in C$ assigns $e$ with $\hat\sigma(e)=\sigma(e)$. Then
--
--   1. $\mathrm{load}_i(\sigma^{-1}(i))\le\sum_{\hat\sigma\in C}\mathrm{load}_i(\hat\sigma^{-1}(i))$ for every $i\in[m]$;
--   2. $g(\mathrm{load}(\sigma))\le\sum_{\hat\sigma\in C} g(\mathrm{load}(\hat\sigma))$;
--   3. if $g(\mathrm{load}(\hat\sigma))\le B$ for every $\hat\sigma\in C$, then $g(\mathrm{load}(\sigma))\le |C|\cdot B$.
--
--   With $B=(1+\epsilon)\mathrm{OPT}$ and $|C|\le\frac1\alpha\ln n$, item 3 is the final bound of Lemma 3.4.
--
--   Differences from the source:
--   - correction: a cover C → a nonempty cover (Nonempty ι); reason: counterexample: U = ∅, C = ∅, load_i(∅) = 1 (Definition 1.2 does not normalize loads); the left side of item 1 is 1 and the empty sum is 0
--   - generalization: g(load(σ)) ≤ Σ_{σ̂∈C} g(load(σ̂)) ≤ ((1+ϵ)/α) ln n OPT, using g(load(σ̂)) ≤ (1+ϵ) OPT and |C| ≤ (1/α) ln n → g(load(σ)) ≤ |C|·B whenever every g(load(σ̂)) ≤ B; reason: specializes with B = (1+ϵ) OPT and |C| ≤ (1/α) ln n; the count |C| itself is milestone lemma_3_5_round_count
--   - generalization: the cover C, a set of assignments → an indexed family C : ι → U → Option (Fin m), repetitions counted in the sums; reason: a set is an injective family, so the statement specializes to the source's
--   - encoding: monotone symmetric norms on the orthant R^k_{≥0} → R_{≥0} → functions (Fin k → ℝ) → ℝ satisfying the public SymNormLoad.IsMonotoneSymmetricNorm (a norm on all of ℝ^k, monotone on the orthant); reason: every monotone symmetric norm on the orthant extends to ℝ^k by x ↦ g(|x|), and only orthant values are ever used; same instances
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), proof of Lemma 3.4, Step 2: Aggregation, p.7 (PDF 9)

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn
import Definitions.Def_GreedNorm_partialLoadVec

namespace GreedNorm

/-- **Aggregating a cover into one assignment** (the proof of Lemma 3.4, Step 2, corrected:
nonempty cover).
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), proof of Lemma 3.4, "Step 2: Aggregation", p.7 (PDF 9): "For each element e, let σ̂ be an
arbitrary assignment in the cover C that assigns e and set σ(e) = σ̂(e). [...] for each i ∈ [m],
we have that σ−1(i) ⊆ ⋃_{σ̂∈C} σ̂−1(i). Monotonicity and subadditivity of loadi implies that
loadi(σ) ≤ Σ_{σ̂∈C} loadi(σ̂), By monotonicity and subadditivity of g, we get
g(load(σ)) ≤ Σ_{σ̂∈C} g(load(σ̂)) ≤ ((1 + ϵ)/α) ln n OPT, where the inequality follows from the
fact that g(load(σ̂)) ≤ (1 + ϵ) OPT for every σ̂ ∈ C and |C| ≤ (1/α) ln n".

Let the loads be nonnegative, monotone and subadditive, `g` a monotone symmetric norm, `C` a
nonempty finite family of partial assignments, and `σ` a total assignment such that every
element `e` has some `σ̂ ∈ C` with `σ̂(e) = σ(e)`. Then
1. `load_i(σ^{-1}(i)) ≤ Σ_{σ̂∈C} load_i(σ̂^{-1}(i))` for every `i`;
2. `g(load(σ)) ≤ Σ_{σ̂∈C} g(load(σ̂))`;
3. if `g(load(σ̂)) ≤ B` for every `σ̂ ∈ C`, then `g(load(σ)) ≤ |C| · B` (with `B = (1+ϵ) OPT` and
   `|C| ≤ (1/α) ln n` this is the page's last inequality).

**Formalization Note** The cover is an indexed family `C : ι → U → Option (Fin m)` over a
nonempty finite `ι` (repetitions are counted in the sums, which is more general than a set).
Subadditivity is the public `SubmodOrder.Subadditive`. -/
theorem lemma_3_4_aggregation {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}
    (load : Fin m → Finset U → ℝ) (hnn : ∀ i S, 0 ≤ load i S)
    (hmono : ∀ i, SubsamplingSM.Offline.IsMonotoneSetFn (load i))
    (hsub : ∀ i, SubmodOrder.Subadditive (load i))
    (g : (Fin m → ℝ) → ℝ) (hg : SymNormLoad.IsMonotoneSymmetricNorm g)
    {ι : Type} [Fintype ι] [Nonempty ι] (C : ι → U → Option (Fin m)) (σ : U → Fin m)
    (hσ : ∀ e, ∃ c, C c e = some (σ e)) :
    (∀ i, partialLoadVec load (fun e => some (σ e)) i ≤ ∑ c, partialLoadVec load (C c) i) ∧
      g (partialLoadVec load (fun e => some (σ e))) ≤ ∑ c, g (partialLoadVec load (C c)) ∧
      ∀ B : ℝ, (∀ c, g (partialLoadVec load (C c)) ≤ B) →
        g (partialLoadVec load (fun e => some (σ e))) ≤ (Fintype.card ι : ℝ) * B := by sorry

end GreedNorm
