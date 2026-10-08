-- Prove2me | Theorems.Thm_FuzzyExtractors_LowerBound_lemma_C_1_T_isCode
-- name    : FuzzyExtractors.LowerBound.lemma_C_1_T_isCode
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:40.009363+00:00
-- url     : https://prove2.me/theorems/66f79eb8-460d-4157-9a31-fbc4087851b4
-- title:
--   Proof of Lemma C.1 — the points producing a fixed sketch value form a code of error-correcting distance t
-- statement:
--   Let $\mathcal M$ be a finite metric space with integer-valued distance $\mathrm{dis}$, and let $(\mathsf{SS},\mathsf{Rec})$ satisfy the correctness property of a secure sketch for $t$ errors: if $\mathrm{dis}(w,w')\le t$ and $s$ is a possible output of $\mathsf{SS}(w)$, then $\mathsf{Rec}(w',s)=w$. Then for every $S\subseteq\mathcal M$ and every sketch value $v$, the set
--   $$T = \{\,w\in S : \Pr[\mathsf{SS}(w)=v]>0\,\}$$
--   is an $(\mathcal M,|T|,t)$-code: for every $w'\in\mathcal M$, at most one element of $T$ lies within distance $t$ of $w'$.
--
--   This is the step of the proof of Lemma C.1 that converts the correctness of the sketch into a packing of balls.
--
--   **Formalization Note** The metric axioms of §2.1 are explicit hypotheses. Symmetry is used because the ball condition measures $\mathrm{dis}(w',c)$ while correctness is stated for $\mathrm{dis}(c,w')$; zero distance and the triangle inequality carry the paper's standing metric assumption.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Appendix C, proof of Lemma C.1, pp. 40–41, "We claim that these 2^{m′} values of w form a code of error-correcting distance t"

import Mathlib
import Definitions.Def_FuzzyExtractors_LowerBound_Basic

namespace FuzzyExtractors.LowerBound

/-- Appendix C, proof of Lemma C.1, pp. 40–41: for a sketch with the correctness property for
distance `t` in a finite metric space, the points of `S` that can produce a fixed sketch value
`v` form a code of error-correcting distance `t`. -/
theorem lemma_C_1_T_isCode {M V : Type} [Fintype M] (dis : M → M → ℕ)
    (hzero : ∀ x y, dis x y = 0 ↔ x = y)
    (hsymm : ∀ x y, dis x y = dis y x)
    (htri : ∀ x y z, dis x z ≤ dis x y + dis y z)
    (t : ℕ) (SS : M → PMF V) (Rec : M → V → PMF M)
    (hcorr : FuzzyExtractors.Hamming.SketchCorrect dis t SS Rec) (S : Finset M) (v : V) :
    FuzzyExtractors.Hamming.IsCode dis (producers SS S v) t := by sorry

end FuzzyExtractors.LowerBound
