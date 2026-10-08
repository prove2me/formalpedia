-- Prove2me | Theorems.Thm_FuzzyExtractors_ImprovedJS_pLow_unique
-- name    : FuzzyExtractors.ImprovedJS.pLow_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:31.659372+00:00
-- url     : https://prove2.me/theorems/d704a720-da5f-4dca-8acc-311ba9350553
-- title:
--   §6.2, p. 21 — the polynomial found in Step 3 of $\mathsf{Rec}$ is unique
-- statement:
--   Let $\mathcal F$ be a field, $t\le s$ natural numbers, $w'\subseteq\mathcal F$ with $|w'|=s$, and $b:\mathcal F\to\mathcal F$ any assignment of target values. If $p_1,p_2\in\mathcal F[z]$ both have degree at most $s-t-1$ and each satisfies $p_j(x)=b(x)$ for at least $s-t/2$ points $x\in w'$, then
--
--   $$p_1 = p_2.$$
--
--   This is the uniqueness half of the decoding step: the polynomial $p_{\mathrm{low}}$ that $\mathsf{Rec}$ looks for in Step 3 of Construction 5 is determined by its input.
--
--   **Formalization Note.** The paper's sentence reads "no two distinct polynomials of degree $s-t-1$ can get the correct $b_i$ on **more than** $s-t/2$ $a_i$s"; the argument it gives ("else, they agree on at least $s-t$ points") and the use in Step 3 need **at least** $s-t/2$, which is what is stated here. "At least $s-t/2$" is doubled to $2\cdot\#\ge 2s-t$, and "degree at most $s-t-1$" is `degree < s - t`. The target values $b$ are arbitrary (in the application $b=p_{\mathrm{high}}$). The paper leaves $t\le s$ implicit; it is a hypothesis here.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, §6.2, analysis of Construction 5, p. 21, "That polynomial is unique, since no two distinct polynomials of degree s−t−1 …"

import Mathlib
import Definitions.Def_FuzzyExtractors_ImprovedJS_Basic
open Polynomial

namespace FuzzyExtractors.ImprovedJS

/-- Construction 5 analysis (p. 21): two polynomials of degree at most s − t − 1 that each agree
with prescribed values b on at least s − t/2 points of an s-element set w′ (doubled:
2·#agreements ≥ 2s − t) are equal. -/
theorem pLow_unique {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] (s t : ℕ) (hts : t ≤ s)
    (w' : Finset 𝔽) (hw' : w'.card = s) (b : 𝔽 → 𝔽) (p₁ p₂ : 𝔽[X])
    (hdeg₁ : p₁.degree < ((s - t : ℕ) : WithBot ℕ))
    (hdeg₂ : p₂.degree < ((s - t : ℕ) : WithBot ℕ))
    (hagree₁ : 2 * s - t ≤ 2 * (w'.filter fun x => p₁.eval x = b x).card)
    (hagree₂ : 2 * s - t ≤ 2 * (w'.filter fun x => p₂.eval x = b x).card) :
    p₁ = p₂ := by sorry

end FuzzyExtractors.ImprovedJS
