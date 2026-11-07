-- Prove2me | Theorems.Thm_MMSDelta2_lemma_7_13
-- name    : MMSDelta2.lemma_7_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:01:56.302638+00:00
-- url     : https://prove2.me/theorems/0480b2f0-f68d-4ad6-ab80-ac43d8c0892e
-- title:
--   Lemma 7.13 — correctness of the reduction
-- statement:
--   Let $(W,T)$ be an instance of LexMax4Partition-Promise, so that it admits a solution. The five-agent goods instance constructed from it admits an MMS allocation if and only if the last bit of the incidence string of the lexicographically maximum solution is $1$:
--
--   $$\text{the constructed instance admits an MMS allocation}\iff \mathrm{inc\text{-}mat}(\mathcal S^*)_{\ell,4\ell}=1.$$
--
--   Together with Lemmas 7.1 and 7.14 this gives the $\Delta_2^P$-hardness of MMS existence for five agents.
--
--   Differences from the source:
--   - encoding: the §7 standing promise: the source instance admits a solution → hypothesis I.HasSolution; reason: LexMax4Partition-Promise instances are promised to admit a solution, and OPT is defined only then
--   - encoding: the last bit of the lexicographically maximum solution is one → ∃ σ lexicographically maximum with (incString σ).getLast? = some true; reason: the lexicographically maximum incidence string is unique, since it determines the solution
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Lemma 7.13, p.35 (PDF p.37); proof pp.35–37

import Mathlib
import Definitions.Def_MMSDelta2_buildInstance
import Definitions.Def_MMSDelta2_HasMMSAllocation

namespace MMSDelta2

/-- **Lemma 7.13**, p.35 (PDF p.37); proof pp.35–37.

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

The constructed goods instance admits an MMS allocation if and only if the last bit of the
lexicographically maximum solution of the source LexMax4Partition-Promise instance is one.

**Formalization Note.** The source instance satisfies the promise (it has a solution).
`LastBitOne` says that the lexicographically maximum incidence string ends with `1`. -/
theorem lemma_7_13 (I : FourPartInstance) (hI : I.HasSolution) :
    HasMMSAllocation I.buildInstance ↔ I.LastBitOne := by sorry

end MMSDelta2
