-- Prove2me | Theorems.Thm_MMSDelta2_theorem_1_1
-- name    : MMSDelta2.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:25.660202+00:00
-- url     : https://prove2.me/theorems/3c76ed5a-9f61-4297-b28e-4a81c690198e
-- title:
--   Theorem 1.1 — MMS existence for additive goods is $\Delta_2^P$-complete, even for five agents
-- statement:
--   Deciding whether an additive goods instance admits an MMS allocation is $\Delta_2^P$-complete, and this remains true for instances with exactly five agents. Precisely, both
--
--   $$\mathrm{MMS}\quad\text{and}\quad\mathrm{MMS}_5$$
--
--   are $\Delta_2^P$-complete, where $\mathrm{MMS}$ is the language of (codes of) additive instances with $n\ge1$ agents, any number of goods and nonnegative rational item values that admit an MMS allocation, and $\mathrm{MMS}_5$ is its restriction to five agents. Here $\Delta_2^P=\mathrm P^{\mathrm{NP}}$ and hardness is under polynomial-time many-one reductions.
--
--   This is the main result of the paper (restated as Theorem 7.15): it settles the complexity of deciding the existence of MMS allocations, with membership due to Lonc and Truszczynski.
--
--   Differences from the source:
--   - encoding: Δ₂ᴾ = P^NP and many-one reductions in a 'standard' unspecified machine model → Δ₂ᴾ = ⋃_{A ∈ NP} P^A with Cook one-tape machines (CookPvsNP.NP, PolyReducible) and the KarpLiptonOM oracle machine (InP); reason: the paper fixes no machine model; these are standard polynomially equivalent models, and a polynomial-time oracle machine makes polynomially many adaptive queries
--   - reading: Δ₂ᴾ-complete, even for five agents → Delta2PComplete MMSLang ∧ Delta2PComplete MMSLang5; reason: the stronger reading: completeness for the general problem and for its five-agent restriction (membership and hardness for both)
--   - encoding: an additive goods instance given explicitly → instCode n m v with v : Fin n → Fin m → ℚ, all v i g ≥ 0, n ≥ 1; non-codes are not in the languages; reason: the paper fixes no encoding; the code is injective and polynomial-time decodable; n ≥ 1 excludes only the instance without agents
--   - encoding: MMS_i over Π_n(M) and allocations → CutChoose.mu over labelled, possibly empty bundles; RRFair.IsAllocation (disjoint, covering); reason: the paper's definitions on p.1
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Theorem 1.1, p.3 (PDF p.5) = Theorem 7.15, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_MMSDelta2_Delta2P
import Definitions.Def_MMSDelta2_MMSLang

namespace MMSDelta2

/-- **Theorem 1.1**, p.3 (PDF p.5) = **Theorem 7.15**, p.37 (PDF p.39).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

Deciding whether an additive goods instance admits an MMS allocation is `Δ₂ᴾ`-complete, even for
five agents.

**Formalization Note.** Both languages are complete: `MMSLang` (any `n ≥ 1` agents) and
`MMSLang5` (exactly five agents), each the set of binary codes of additive instances with
nonnegative rational item values and any number of goods that admit an MMS allocation.
`Δ₂ᴾ = P^NP` on the published Cook and oracle machines; hardness is by polynomial-time many-one
reductions from every `Δ₂ᴾ` language. -/
theorem theorem_1_1 : Delta2PComplete MMSLang ∧ Delta2PComplete MMSLang5 := by sorry

end MMSDelta2
