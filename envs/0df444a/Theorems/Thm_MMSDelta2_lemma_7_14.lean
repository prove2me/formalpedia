-- Prove2me | Theorems.Thm_MMSDelta2_lemma_7_14
-- name    : MMSDelta2.lemma_7_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:03:26.460012+00:00
-- url     : https://prove2.me/theorems/8e1206bd-3c9b-4aa2-ae17-3dfd5eafe312
-- title:
--   Lemma 7.14 — the reduction runs in polynomial time
-- statement:
--   The reduction of §7 can be executed in polynomial time. Precisely, the map on binary strings that sends the code of a 4-PARTITION instance to the code of the constructed five-agent goods instance (and every other string to a fixed non-code) is computable in polynomial time, and on the code of every 4-PARTITION instance it outputs the code of the constructed instance.
--
--   With Lemmas 7.1 and 7.13 this completes the hardness proof of Theorem 7.15.
--
--   Differences from the source:
--   - generalization: polynomial time on the instances of Lemma 7.1, with T and every number O(q⁴) (the proof uses this bound) → polynomial time on every binary input, with no bound on T; reason: all numbers of the construction have bit length polynomial in ℓ and log T, so the bound is not needed; the bounded instances are a special case
--   - encoding: 'the reduction' → the map reduction : List Bool → List Bool, with the clause reduction (fourPartCode I) = instCode 5 _ I.buildInstance; non-codes map to [true]; reason: ties the polynomial-time claim to the §7 construction; [true] has odd length, so it is no instance code
--   - encoding: Δ₂ᴾ = P^NP and many-one reductions in a 'standard' unspecified machine model → Δ₂ᴾ = ⋃_{A ∈ NP} P^A with Cook one-tape machines (CookPvsNP.NP, PolyReducible) and the KarpLiptonOM oracle machine (InP); reason: the paper fixes no machine model; these are standard polynomially equivalent models, and a polynomial-time oracle machine makes polynomially many adaptive queries
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Lemma 7.14, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_MMSDelta2_reduction

namespace MMSDelta2

/-- **Lemma 7.14**, p.37 (PDF p.39).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

The reduction can be executed in polynomial time.

**Formalization Note.** The reduction is the map `reduction` on binary strings; the item states
that it is polynomial-time computable (published `CookPvsNP.PolyTimeComputable`) and that on the
code of every 4-PARTITION instance it outputs the code of the constructed five-agent instance.
The paper's proof uses the `O(q⁴)` bound of Lemma 7.1; on binary input the reduction runs in
polynomial time without it, so no bound is assumed. -/
theorem lemma_7_14 :
    CookPvsNP.PolyTimeComputable reduction ∧
      ∀ I : FourPartInstance, reduction (fourPartCode I) = instCode 5 _ I.buildInstance := by sorry

end MMSDelta2
