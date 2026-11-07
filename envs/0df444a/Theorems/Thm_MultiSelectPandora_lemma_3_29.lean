-- Prove2me | Theorems.Thm_MultiSelectPandora_lemma_3_29
-- name    : MultiSelectPandora.lemma_3_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:29:32.063477+00:00
-- url     : https://prove2.me/theorems/931ac391-92da-4689-8c87-083e026c294e
-- title:
--   Lemma 3.29 — the loss of the discretization: $\mathrm{OPT}^{SL}\ge(1-O(k\varepsilon))\mathrm{OPT}$
-- statement:
--   There are absolute constants $C,\varepsilon_0>0$, not depending on $k$, such that for $0<\varepsilon\le\varepsilon_0$, $k\ge1$ and every valid instance with $0<\mathrm{OPT}$,
--   $$\mathrm{OPT}_{I^{SL}}\ge(1-Ck\varepsilon)\,\mathrm{OPT}.$$
--   For constant $k$ this is $(1-O(\varepsilon))\mathrm{OPT}$. The proof gives $C=11$ and $\varepsilon_0=1/4$.
--
--   Differences from the source:
--   - reading: O(kε) → ∃ C, ε₀ before k and the instance; reason: the constant is absolute in the proof; ε small is what Theorem 1.1 needs
--   - encoding: no hypothesis on OPT → 0 < OPT; reason: θ = OPT^/ε is 0 when OPT = 0 and p.14 divides by it, so this excludes only an undefined case
--   - reading: the grid of Definition 3.21 written with ε OPT → the grid with ε OPT^; reason: footnote 1: "the algorithm uses ε OPT^", as OPT is not known; Φ changes by at most 2ε OPT within a cell
--   - reading: ⊤ is "an arbitrary fixed number greater than MaxV" (footnote 2) → ⊤ is a number above MaxV and above every value of the instance; reason: Remark A.4 and Claim A.7 need D^L(v) ≥ v for every v; with ⊤ = MaxV + 1 Claim 3.30 fails (two boxes, value 1000 with probability 0.1, else 0, c = 90, k = 1, ε = 1/4; gap 5.23)
--   - reading: σi "the solution" of E[(vi − σi)+] = ci → the least solution; reason: the solution is not unique when ci = 0; κi is the same for every choice
--   - encoding: a law Fi with finite support → explicit support positions with values and probabilities, and expectations as finite sums with independence by product form; reason: p.5: "Each Fi is given explicitly, with finite support"
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Lemma 3.29, p.17 (PDF p.18); proof pp.34–35 (PDF pp.35–36)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_Valid
import Definitions.Def_MultiSelectPandora_OPT
import Definitions.Def_MultiSelectPandora_ISL
import Definitions.Def_MultiSelectPandora_DPData_value

namespace MultiSelectPandora

/-- **Lemma 3.29 (loss of the discretization)**, p.17 (PDF p.18); proof pp.34–35 (PDF pp.35–36). Beyhaghi–Han–Luqman manuscript.

`OPT^SL ≥ (1 − O(kε)) OPT`.

**Formalization Note.** `C` is absolute, before `k`. The proof gives `C = 11`, `ε₀ = 1/4` (`2kε + 6ε + 3ε ≤ 11kε`). The clause "which is `(1 − O(ε)) OPT` for constant `k`" is immediate. -/
theorem lemma_3_29 :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ k : ℕ, 1 ≤ k → ∀ I : Inst, I.Valid →
      0 < OPT I k →
        (1 - C * k * ε) * OPT I k ≤ (ISL I k ε).value Finset.univ (0 : Fin k → ℝ) := by sorry

end MultiSelectPandora
