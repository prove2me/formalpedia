-- Prove2me | Theorems.Thm_FuzzyExtractors_ImprovedJS_rec_correct
-- name    : FuzzyExtractors.ImprovedJS.rec_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:46.387799+00:00
-- url     : https://prove2.me/theorems/eb39a674-04a4-4c21-9eda-bee71c9e51bc
-- title:
--   §6.2, p. 21 — $\mathsf{Rec}(w',\mathsf{SS}(w)) = w$ whenever $|w\triangle w'|\le t$
-- statement:
--   Let $\mathcal F$ be a field and $t\le s$ natural numbers. For all $s$-element sets $w,w'\subseteq\mathcal F$ with $\mathrm{dis}(w,w')=|w\triangle w'|\le t$, the recovery procedure of Construction 5 returns the original set:
--
--   $$\mathsf{Rec}\big(w',\mathsf{SS}(w)\big) = w.$$
--
--   That is, Construction 5 satisfies the correctness property of a secure sketch (Definition 3, item 2) on $\mathrm{SDif}_s(\mathcal F)$ with threshold $t$. Together with the entropy bound, this is the correctness half of Theorem 6.1.
--
--   **Formalization Note.** Both procedures are deterministic, so "returns $w$" is `Rec w' (SS w) = PMF.pure w`. The default output used for the paper's "fail" plays no role here, since the statement is about inputs within distance $t$. The paper leaves $t\le s$ implicit; it is a hypothesis here.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, §6.2, analysis of Construction 5, p. 21, "Therefore, the recovered polynomial p_low must be −q … which consists of the roots of p′"

import Mathlib
import Definitions.Def_FuzzyExtractors_ImprovedJS_Basic

namespace FuzzyExtractors.ImprovedJS

/-- Construction 5 analysis (p. 21): Rec recovers w from w′ and SS(w) whenever dis(w, w′) ≤ t,
i.e. Construction 5 satisfies the correctness property of a secure sketch on SDif_s(𝔽). -/
theorem rec_correct {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] (s t : ℕ) (hts : t ≤ s) :
    FuzzyExtractors.Hamming.SketchCorrect (sdifDist (𝓤 := 𝔽) (s := s)) t (sketch s t) (recover s t) := by sorry

end FuzzyExtractors.ImprovedJS
