-- Prove2me | Theorems.Thm_GreedNorm_lemma_3_12_feasibility
-- name    : GreedNorm.lemma_3_12_feasibility
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:12.193122+00:00
-- url     : https://prove2.me/theorems/a5f25805-0c4c-43b9-8d79-e0eab34892ee
-- title:
--   Proof of Lemma 3.12 — when $\mathcal A\cup\{(i,S)\}$ stays valid and $t$-bounded (corrected: largest tight $\ell$, $(i,S)\notin\mathcal A$)
-- statement:
--   Let $\epsilon>0$, $t$ a threshold vector, $\mathcal A$ a valid and $t$-bounded configuration set, and $(i,S)\notin\mathcal A$ a configuration. Call $\ell\in\mathrm{POS}$ **tight** if the number of $(i',S')\in\mathcal A$ with $\mathrm{load}_{i'}(S')>t_\ell$ equals $\ell-1$. Then
--
--   1. $\mathcal A\cup\{(i,S)\}$ is valid if and only if $\mathcal A$ has no configuration of type $i$;
--   2. there is a largest tight $\ell^*\in\mathrm{POS}$, and $\mathcal A\cup\{(i,S)\}$ is valid and $t$-bounded if and only if $\mathcal A$ has no configuration of type $i$ and
--
--   $$
--   \mathrm{load}_i(S)\le t_{\ell^*}.
--   $$
--
--   So the augmentation problem reduces to BudgCard instances with budget $t_{\ell^*}$, one per type not in $\mathcal A$.
--
--   **Formalization Note** Since $t$ is non-increasing, $\mathrm{load}_i(S)\le t_{\ell^*}$ for the largest tight $\ell^*$ is equivalent to $\mathrm{load}_i(S)\le t_\ell$ for every tight $\ell$. $\ell=1$ is tight (footnote 4), so $\ell^*$ exists.
--
--   Differences from the source:
--   - correction: ℓ* is the smallest tight ℓ ∈ POS → ℓ* is the largest tight ℓ ∈ POS (whose existence is also asserted); reason: counterexample: m = 2, POS = {1, 2}, t_1 = 10, t_2 = 1, U = {a, b}, load_1({a}) = load_2({b}) = 5; A = {(1, {a})} is valid and t-bounded, the smallest tight ℓ is 1 and load_2({b}) ≤ t_1, but A ∪ {(2, {b})} has two configurations of load > t_2 = 1, more than 2 − 1 (checked in the sanity file)
--   - correction: A ∪ {(i, S)} for any configuration (i, S) → hypothesis (i, S) ∉ A; reason: counterexample: A = {(i, S)} is valid and A ∪ {(i, S)} = A is valid, yet A has a configuration of type i, so item 1 fails; augmentations add new configurations
--   - generalization: Lemma 3.12's hypothesis "let t be a good threshold vector" → any threshold vector t; reason: the two equivalences of the proof never use goodness (the existence of a t-bounded assignment); good threshold vectors are among these, so the statement specializes to the source's
--   - generalization: load functions load_i : 2^U → R_{≥0} (Definition 1.2) → arbitrary real-valued load : Fin m → Finset U → ℝ; reason: the counting argument does not use the sign of the loads; nonnegative loads are among these
--   - encoding: configurations (i, S), i ∈ [m], S ⊆ U; configuration sets → Fin m × Finset U (types 0-based); Finset of configurations; reason: Lean convention; same instances
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), proof of Lemma 3.12 and footnote 4, p.9 (PDF 11)

import Mathlib
import Definitions.Def_GreedNorm_POS
import Definitions.Def_GreedNorm_IsThreshold
import Definitions.Def_GreedNorm_IsValidConf
import Definitions.Def_GreedNorm_IsTBoundedConf

namespace GreedNorm

/-- **The feasibility test for augmenting a valid `t`-bounded configuration set** (the proof of
Lemma 3.12, corrected: the *largest* tight `ℓ`).
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), proof of Lemma 3.12, p.9 (PDF 11): "Observe that A ∪ {(i, S)} is valid if and only if A does
not already have a configuration of type i. Observe also that A ∪ {(i, S)} is valid and t-bounded
if and only if A does not already have a configuration of type i and loadi(S) ≤ tℓ∗ where ℓ∗ is
the smallest ℓ ∈ POS such that the number of configurations (i, S) ∈ A with loadi(S) > tℓ is
equal to ℓ−1." Footnote 4: "Note that ℓ = 1 satisfies the condition."

Let `t` be a threshold vector, `A` valid and `t`-bounded, and `(i,S) ∉ A`. Then
1. `A ∪ {(i,S)}` is valid iff no configuration of `A` has type `i`;
2. there is a largest `ℓ* ∈ POS` that is *tight*, i.e. `#{c ∈ A : load(c) > t_ℓ*} = ℓ* − 1`, and
   `A ∪ {(i,S)}` is valid and `t`-bounded iff no configuration of `A` has type `i` and
   `load_i(S) ≤ t_ℓ*`.

**Formalization Note** The page's "smallest" is replaced by "largest" (see the differences
list); since `t` is non-increasing, `load_i(S) ≤ t_ℓ*` for the largest tight `ℓ*` is the same
as `load_i(S) ≤ t_ℓ` for every tight `ℓ`. `(i,S) ∉ A` makes `A ∪ {(i,S)}` a set with one
more configuration (`insert` on a `Finset`). Since `i : Fin m`, `m ≥ 1`, so `1 ∈ POS`. -/
theorem lemma_3_12_feasibility {U : Type} [Fintype U] [DecidableEq U] {m : ℕ} (ε : ℝ) (hε : 0 < ε) (t : ℕ → ℝ) (ht : IsThreshold m ε t) (load : Fin m → Finset U → ℝ)
    (A : Finset (Fin m × Finset U)) (hA : IsValidConf A) (hAt : IsTBoundedConf ε load t A)
    (i : Fin m) (S : Finset U) (hiS : (i, S) ∉ A) :
    (IsValidConf (insert (i, S) A) ↔ ∀ c ∈ A, c.1 ≠ i) ∧
      ∃ ℓs ∈ POS m ε, (A.filter (fun c => t ℓs < load c.1 c.2)).card = ℓs - 1 ∧
        (∀ ℓ ∈ POS m ε, (A.filter (fun c => t ℓ < load c.1 c.2)).card = ℓ - 1 → ℓ ≤ ℓs) ∧
        (IsValidConf (insert (i, S) A) ∧ IsTBoundedConf ε load t (insert (i, S) A) ↔
          (∀ c ∈ A, c.1 ≠ i) ∧ load i S ≤ t ℓs) := by sorry

end GreedNorm
