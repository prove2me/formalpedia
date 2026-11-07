-- Prove2me | Theorems.Thm_MMSDelta2_lemma_A_1
-- name    : MMSDelta2.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:23.637728+00:00
-- url     : https://prove2.me/theorems/ecb442ce-cf18-41ca-9c5f-17cce01f5f42
-- title:
--   Lemma A.1 — LexMaxSAT-Promise is $\Delta_2^P$-hard
-- statement:
--   LexMaxSAT-Promise asks, for a CNF formula $\varphi(x_1,\dots,x_n)$ promised to be satisfiable, whether $x_n=1$ in its lexicographically largest satisfying assignment. This promise problem is $\Delta_2^P$-hard: every language in $\Delta_2^P$ has a polynomial-time many-one map sending its members to yes-instances and its non-members to no-instances.
--
--   It is the second step of the chain LexMaxSAT → LexMaxSAT-Promise → LexMax3SAT-Promise → LexMax4Partition-Promise.
--
--   Differences from the source:
--   - encoding: Δ₂ᴾ = P^NP and many-one reductions in a 'standard' unspecified machine model → Δ₂ᴾ = ⋃_{A ∈ NP} P^A with Cook one-tape machines (CookPvsNP.NP, PolyReducible) and the KarpLiptonOM oracle machine (InP); reason: the paper fixes no machine model; these are standard polynomially equivalent models, and a polynomial-time oracle machine makes polynomially many adaptive queries
--   - encoding: Δ₂ᴾ-hardness of a promise problem (not defined in the paper) → Delta2PHardPromise: a polynomial-time f with x ∈ L' ⇒ f x ∈ Π_YES and x ∉ L' ⇒ f x ∈ Π_NO, for every L' ∈ Δ₂ᴾ; reason: the standard notion, and the one the proof constructs
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Lemma A.1, p.53 (PDF p.55)

import Mathlib
import Definitions.Def_MMSDelta2_Delta2P
import Definitions.Def_MMSDelta2_LexMaxSAT

namespace MMSDelta2

/-- **Lemma A.1**, p.53 (PDF p.55).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

LexMaxSAT-Promise is `Δ₂ᴾ`-hard.

**Formalization Note.** LexMaxSAT-Promise is the promise problem `LexMaxSATPromise` whose
promise is that the formula is satisfiable; hardness of a promise problem means that every `Δ₂ᴾ`
language has a polynomial-time many-one map sending members into its yes-instances and
non-members into its no-instances (`Delta2PHardPromise`). -/
theorem lemma_A_1 : Delta2PHardPromise LexMaxSATPromise := by sorry

end MMSDelta2
