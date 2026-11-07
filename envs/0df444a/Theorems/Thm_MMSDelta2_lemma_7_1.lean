-- Prove2me | Theorems.Thm_MMSDelta2_lemma_7_1
-- name    : MMSDelta2.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:00.878331+00:00
-- url     : https://prove2.me/theorems/a59b7525-2ca1-4987-bacd-24360e829d14
-- title:
--   Lemma 7.1 — LexMax4Partition-Promise is $\Delta_2^P$-hard with $T=O(q^4)$
-- statement:
--   There is a constant $C$ such that LexMax4Partition-Promise is $\Delta_2^P$-hard even when restricted to instances with $4q$ numbers whose target satisfies $T\le C\,q^4$. Since every number $w_j$ satisfies $w_j<T/3$, every number is then $O(q^4)$ as well.
--
--   This is the source problem of the final reduction to MMS existence; the polynomial bound makes the source numbers polynomially bounded.
--
--   Differences from the source:
--   - encoding: Δ₂ᴾ = P^NP and many-one reductions in a 'standard' unspecified machine model → Δ₂ᴾ = ⋃_{A ∈ NP} P^A with Cook one-tape machines (CookPvsNP.NP, PolyReducible) and the KarpLiptonOM oracle machine (InP); reason: the paper fixes no machine model; these are standard polynomially equivalent models, and a polynomial-time oracle machine makes polynomially many adaptive queries
--   - encoding: Δ₂ᴾ-hardness of a promise problem → Delta2PHardPromise; reason: the standard notion, and the one the proof constructs
--   - reading: restricted to instances in which the target T and every number are O(q⁴) → ∃ C, the promise includes T ≤ C·q⁴ for every instance; numbers are then < T/3 ≤ C·q⁴; reason: a uniform bound for all q ≥ 1 is the stronger reading of O(q⁴) (a smaller promise set), and the proof gives T = 40(32s)⁴ + 15 ≤ (40·32⁴ + 15)·q⁴ for all q ≥ 1
--   - encoding: a multiset W and ordered tuples of submultisets → indexed numbers w : Fin (4q) → ℕ and solutions σ : Fin (4q) → Fin q; reason: inc-mat refers to the numbers by index i, so the multiset is indexed; σ determines and is determined by the tuple
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Lemma 7.1 (†), p.27 (PDF p.29); proof pp.53–56 (PDF pp.55–58)

import Mathlib
import Definitions.Def_MMSDelta2_Delta2P
import Definitions.Def_MMSDelta2_FourPartition

namespace MMSDelta2

/-- **Lemma 7.1 (†)**, p.27 (PDF p.29); proof pp.53–56 (PDF pp.55–58).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

LexMax4Partition-Promise is `Δ₂ᴾ`-hard even when restricted to instances with `4q` numbers in
which the target `T` and every number are `O(q⁴)`.

**Formalization Note.** "`O(q⁴)`" is a constant `C` with `T ≤ C·q⁴` on every instance of the
restricted problem `LexMax4PartPromise C` (its yes- and no-instances). Every number is below
`T/3`, so the bound on `T` bounds every number too. Hardness is `Delta2PHardPromise`. -/
theorem lemma_7_1 : ∃ C : ℕ, Delta2PHardPromise (LexMax4PartPromise C) := by sorry

end MMSDelta2
