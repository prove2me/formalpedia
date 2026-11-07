-- Prove2me | Theorems.Thm_MMSDelta2_lemma_A_2
-- name    : MMSDelta2.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:07.590319+00:00
-- url     : https://prove2.me/theorems/fad266ed-aa81-48d7-824e-17ee642b246e
-- title:
--   Lemma A.2 — LexMax3SAT-Promise is $\Delta_2^P$-hard
-- statement:
--   LexMax3SAT-Promise is LexMaxSAT-Promise restricted to 3-CNF formulas: given a satisfiable formula in which every clause has at most three literals, decide whether the last variable is $1$ in its lexicographically largest satisfying assignment. This promise problem is $\Delta_2^P$-hard under polynomial-time many-one reductions.
--
--   It is the third step of the reduction chain.
--
--   Differences from the source:
--   - encoding: Δ₂ᴾ = P^NP and many-one reductions in a 'standard' unspecified machine model → Δ₂ᴾ = ⋃_{A ∈ NP} P^A with Cook one-tape machines (CookPvsNP.NP, PolyReducible) and the KarpLiptonOM oracle machine (InP); reason: the paper fixes no machine model; these are standard polynomially equivalent models, and a polynomial-time oracle machine makes polynomially many adaptive queries
--   - encoding: Δ₂ᴾ-hardness of a promise problem → Delta2PHardPromise; reason: the standard notion, and the one the proof constructs
--   - reading: the input formula is a 3-CNF → every clause has at most three literals; reason: the reduction of the proof leaves 'Clauses containing at most three literals … unchanged', so it produces clauses of length ≤ 3
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Lemma A.2, p.53 (PDF p.55)

import Mathlib
import Definitions.Def_MMSDelta2_Delta2P
import Definitions.Def_MMSDelta2_LexMaxSAT

namespace MMSDelta2

/-- **Lemma A.2**, p.53 (PDF p.55).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

LexMax3SAT-Promise is `Δ₂ᴾ`-hard.

**Formalization Note.** LexMax3SAT-Promise (`LexMax3SATPromise`) is LexMaxSAT-Promise restricted
to formulas in which every clause has at most three literals; hardness is `Delta2PHardPromise`. -/
theorem lemma_A_2 : Delta2PHardPromise LexMax3SATPromise := by sorry

end MMSDelta2
