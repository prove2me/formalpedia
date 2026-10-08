-- Prove2me | Theorems.Thm_FuzzyExtractors_ImprovedJS_intersection_bound
-- name    : FuzzyExtractors.ImprovedJS.intersection_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:52.983615+00:00
-- url     : https://prove2.me/theorems/203fc88d-e8d5-4e29-ac89-84eb016c1c19
-- title:
--   §6.2, p. 21 — $|w\cap w'|\ge s-t/2$, so $-q$ satisfies Step 3 of $\mathsf{Rec}$
-- statement:
--   Let $\mathcal F$ be a field, $t\le s$ natural numbers and $w,w'\subseteq\mathcal F$ with $|w|=|w'|=s$ and $|w\triangle w'|\le t$. Then
--
--   1. $w$ and $w'$ have at least $s-t/2$ common points: $$2\,|w\cap w'|\ \ge\ 2s-t;$$
--   2. the polynomial $-q$, where $q=p'-p_{\mathrm{high}}$ for $p'=\prod_{x\in w}(z-x)$ and $p_{\mathrm{high}}$ built from $\mathsf{SS}(w)$, satisfies the condition of Step 3 of $\mathsf{Rec}(w',\mathsf{SS}(w))$ in Construction 5: $\deg(-q)\le s-t-1$ and $-q(x)=p_{\mathrm{high}}(x)$ for at least $s-t/2$ points $x\in w'$.
--
--   This shows that the Reed–Solomon decoding step of the recovery procedure has a solution whenever the input set is within distance $t$ of the original.
--
--   **Formalization Note.** "At least $s-t/2$" is doubled to $2\cdot\#\ge 2s-t$ in $\mathbb N$, which covers odd $t$ (distances in $\mathrm{SDif}_s$ are even). The paper leaves $t\le s$ implicit; it is a hypothesis here.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, §6.2, analysis of Construction 5, p. 21, "Since the set w intersects w′ in at least s−t/2 points, the polynomial −q satisfies the conditions of Step 3 in Rec"; cf. §6, p. 18

import Mathlib
import Definitions.Def_FuzzyExtractors_ImprovedJS_Basic
open Polynomial

namespace FuzzyExtractors.ImprovedJS

/-- Construction 5 analysis (p. 21): if |w| = |w′| = s and |w △ w′| ≤ t, then w and w′ share at
least s − t/2 points (doubled: 2|w ∩ w′| ≥ 2s − t), and −q, where q = p′ − p_high, satisfies the
condition of Step 3 of Rec on input (w′, SS(w)). -/
theorem intersection_bound {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] (s t : ℕ) (hts : t ≤ s)
    (w w' : Finset 𝔽) (hw : w.card = s) (hw' : w'.card = s) (hd : (symmDiff w w').card ≤ t) :
    2 * s - t ≤ 2 * (w ∩ w').card ∧
      Step3Cond s t (sketchCoeffs s t w) w'
        (-(charPoly w - pHigh s t (sketchCoeffs s t w))) := by sorry

end FuzzyExtractors.ImprovedJS
