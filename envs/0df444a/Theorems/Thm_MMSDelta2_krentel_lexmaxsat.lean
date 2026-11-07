-- Prove2me | Theorems.Thm_MMSDelta2_krentel_lexmaxsat
-- name    : MMSDelta2.krentel_lexmaxsat
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:19.965147+00:00
-- url     : https://prove2.me/theorems/13113add-71ae-4b58-a65b-be8e334e6ccd
-- title:
--   [Kre88] (cited) — LexMaxSAT is $\Delta_2^P$-complete
-- statement:
--   Let $\mathrm{LexMaxSAT}$ be the set of (codes of) CNF formulas $\varphi(x_1,\dots,x_n)$, $n\ge1$, whose lexicographically largest satisfying assignment, with $x_1$ most significant and $1>0$, sets the last variable $x_n$ to $1$; unsatisfiable formulas are no-instances. Then
--
--   $$\mathrm{LexMaxSAT}\ \text{is}\ \Delta_2^P\text{-complete}.$$
--
--   This is Krentel's theorem (M. W. Krentel, *The complexity of optimization problems*, J. Comput. System Sci. 36(3) (1988) 490–509), the source of hardness for the reduction chain.
--
--   **Formalization Note** Completeness is membership in $\Delta_2^P$ together with $\Delta_2^P$-hardness under polynomial-time many-one reductions.
--
--   Differences from the source:
--   - encoding: Δ₂ᴾ = P^NP and many-one reductions in a 'standard' unspecified machine model → Δ₂ᴾ = ⋃_{A ∈ NP} P^A with Cook one-tape machines (CookPvsNP.NP, PolyReducible) and the KarpLiptonOM oracle machine (InP); reason: the paper fixes no machine model; these are standard polynomially equivalent models, and a polynomial-time oracle machine makes polynomially many adaptive queries
--   - encoding: a CNF formula φ(x₁, …, xₙ) → n ≥ 1 and a CookPvsNP.CNF with variable indices 0, …, n−1 (index k is x_{k+1}), coded as natCode n followed by encodeCNF in two bits per symbol; non-codes are not in the language; reason: the paper fixes no encoding; n ≥ 1 is needed for x_n to exist
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), [Kre88], cited p.12 (PDF p.14) and p.53 (PDF p.55); M. W. Krentel, J. Comput. System Sci. 36(3) (1988) 490–509

import Mathlib
import Definitions.Def_MMSDelta2_Delta2P
import Definitions.Def_MMSDelta2_LexMaxSAT

namespace MMSDelta2

/-- **[Kre88] (cited)**, stated p.12 (PDF p.14) and p.53 (PDF p.55); M. W. Krentel, *The
complexity of optimization problems*, J. Comput. System Sci. 36(3) (1988) 490–509.

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

"Deciding whether the last variable is set to true in the lexicographically maximum satisfying
assignment is a canonical `Δ₂ᴾ`-complete problem [Kre88]."

**Formalization Note.** `LexMaxSATLang` contains the codes of CNF formulas `φ(x_1, …, x_n)`,
`n ≥ 1`, whose lexicographically largest satisfying assignment (`x_1` most significant, `1 > 0`)
has `x_n = 1`; unsatisfiable formulas are no-instances. Completeness is membership in `Δ₂ᴾ` and
`Δ₂ᴾ`-hardness under polynomial-time many-one reductions. -/
theorem krentel_lexmaxsat : Delta2PComplete LexMaxSATLang := by sorry

end MMSDelta2
