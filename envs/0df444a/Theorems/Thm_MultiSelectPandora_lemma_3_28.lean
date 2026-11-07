-- Prove2me | Theorems.Thm_MultiSelectPandora_lemma_3_28
-- name    : MultiSelectPandora.lemma_3_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:29:42.841196+00:00
-- url     : https://prove2.me/theorems/a6a2e665-93f0-4a66-ad41-bc02c59837ef
-- title:
--   Lemma 3.28 — the whole-continuation bound $O(\varepsilon^2)\mathrm{OPT}$
-- statement:
--   There are absolute constants $C,\varepsilon_0>0$ such that the following holds for $0<\varepsilon\le\varepsilon_0$, $k\ge1$ and every valid instance with $0<\mathrm{OPT}$. Let $\alpha$ be a fully large state of $I^{SL}$, that is $\alpha_k\ge\theta$ and every entry is a grid point or $\top$, and let $U$ be a set of boxes. Then
--   $$G_{I^S}(U,\alpha)-G_{I^{SL}}(U,\alpha)\le C\varepsilon^2\,\mathrm{OPT}.$$
--
--   Repeated rounding of the state thus costs $O(\varepsilon^2)\mathrm{OPT}$ over the whole continuation. The proof gives $C=12$ and $\varepsilon_0=1/4$.
--
--   Differences from the source:
--   - reading: O(ε²) → ∃ C, ε₀ before k and the instance; reason: uniform over instances and over k, as the proof gives; ε small is what Theorem 1.1 needs
--   - reading: "a fully large state of ISL" → every entry a grid point or ⊤, and αk ≥ θ; reason: the states of Definition 3.23; Remark A.4 calls this a hypothesis of the lemma
--   - encoding: no hypothesis on OPT → 0 < OPT; reason: θ = OPT^/ε is 0 when OPT = 0 and p.14 divides by it, so this excludes only an undefined case
--   - reading: the grid of Definition 3.21 written with ε OPT → the grid with ε OPT^; reason: footnote 1: "the algorithm uses ε OPT^", as OPT is not known; Φ changes by at most 2ε OPT within a cell
--   - reading: ⊤ is "an arbitrary fixed number greater than MaxV" (footnote 2) → ⊤ is a number above MaxV and above every value of the instance; reason: Remark A.4 and Claim A.7 need D^L(v) ≥ v for every v; with ⊤ = MaxV + 1 Claim 3.30 fails (two boxes, value 1000 with probability 0.1, else 0, c = 90, k = 1, ε = 1/4; gap 5.23)
--   - reading: σi "the solution" of E[(vi − σi)+] = ci → the least solution; reason: the solution is not unique when ci = 0; κi is the same for every choice
--   - encoding: a law Fi with finite support → explicit support positions with values and probabilities, and expectations as finite sums with independence by product form; reason: p.5: "Each Fi is given explicitly, with finite support"
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Lemma 3.28, p.16 (PDF p.17); proof pp.33–34 (PDF pp.34–35)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_Valid
import Definitions.Def_MultiSelectPandora_OPT
import Definitions.Def_MultiSelectPandora_IsSortedState
import Definitions.Def_MultiSelectPandora_theta
import Definitions.Def_MultiSelectPandora_stFloor
import Definitions.Def_MultiSelectPandora_gridPts
import Definitions.Def_MultiSelectPandora_topLevel
import Definitions.Def_MultiSelectPandora_IS
import Definitions.Def_MultiSelectPandora_ISL
import Definitions.Def_MultiSelectPandora_DPData_value

namespace MultiSelectPandora

/-- **Lemma 3.28 (whole-continuation bound under repeated large rounding)**, p.16 (PDF p.17); proof pp.33–34 (PDF pp.34–35). Beyhaghi–Han–Luqman manuscript.

**Formalization Note.** `O(ε²)` is `∃ C, ∃ ε₀` before `k` and the instance. The proof gives `C = 12`, `ε₀ = 1/4`, with footnote 1's cell `2ε OPT`: `Δ ≤ 6ε OPT` and `μ ≤ 2ε`. "A fully large state of `I^SL`" includes **every entry a grid point** or `⊤` (Remark A.4): the recursion's step relies on it (Lemma A.5(e)). -/
theorem lemma_3_28 :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ k : ℕ, 1 ≤ k → ∀ I : Inst, I.Valid →
      0 < OPT I k → ∀ (U : Finset (Fin I.n)) (α : Fin k → ℝ), IsSortedState α →
        (∀ j, α j ∈ gridPts I k ε ∨ α j = topLevel I k ε) → theta I k ε ≤ stFloor α →
        (IS I k ε).value U α - (ISL I k ε).value U α ≤ C * ε ^ 2 * OPT I k := by sorry

end MultiSelectPandora
