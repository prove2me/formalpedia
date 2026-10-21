-- Prove2me | Theorems.Thm_IncompleteProc_English_lemma_2
-- name    : IncompleteProc.English.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:38.667982+00:00
-- url     : https://prove2.me/theorems/4b06f6cf-63a7-4370-a1ae-5059416cc428
-- title:
--   Lemma 2, p. 16 (PDF 17) — Φ(c) = Φ(c̲) + ∫ φ with φ(c) = −∫_{Ω(c)} Q k_c(c, ω) dG(ω)
-- statement:
--   Let $\Phi(c) = \int_\Omega Q \max\{0, k(c^\star_2(\omega), \omega) - k(c, \omega)\}\, dG(\omega)$ be the expected second-period profit of a supplier with first-period cost $c$ who is offered $k(c^\star_2(\omega), \omega)$. Let $\Omega(c) = \{\omega : k(c, \omega) \le k(c^\star_2(\omega), \omega)\}$ be the set of states in which he produces. Then for every $c \in [\underline c, \bar c]$,
--   $$\Phi(c) = \Phi(\underline c) + \int_{\underline c}^{c} \varphi(s)\, ds, \qquad \varphi(c) = -\int_{\Omega(c)} Q\, k_c(c, \omega)\, dG(\omega). \tag{7, 8}$$
--
--   The lemma identifies the derivative of the expected second-period profit, which is used to compute supplier profits in the auction implementations.
--
--   **Formalization Note** The measurability of $\omega \mapsto c^\star_2(\omega)$, and hence of $\Omega(c)$, is not assumed; it follows from the standing assumptions and Assumption 1.
-- source:
--   Gretschko & Pollrich, Incomplete Contracts in Dynamic Procurement, ZEW Discussion Paper No. 19-040 (Sept. 2019; SSRN 3466701), p. 16 (PDF 17), proof of Proposition 2: Ω(c), Φ, Lemma 2, eqs. (7)–(8)

import Mathlib
import Definitions.Def_IncompleteProc_English_Model

namespace IncompleteProc.English

open MeasureTheory

/-- Lemma 2 (p. 16): for every `c ∈ [c̲, c̄]`, `Φ(c) = Φ(c̲) + ∫_{c̲}^{c} φ(s) ds` (7), with
`φ(c) = −∫_{Ω(c)} Q k_c(c, ω) dG(ω)` (8). -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) :
    ∀ c ∈ Set.Icc E.clo E.chi, E.Phi c = E.Phi E.clo + ∫ s in E.clo..c, E.phi s := by sorry

end IncompleteProc.English
