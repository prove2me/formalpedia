-- Prove2me | Theorems.Thm_IsodiamVar_Simplex_Supplement_lemma_2_3
-- name    : IsodiamVar.Simplex.Supplement.lemma_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:50:40.271986+00:00
-- url     : https://prove2.me/theorems/2b2b5eec-1456-4401-8aa2-26bdfe544db1
-- title:
--   Lemma 2.3 — complete biconjugate translation formula and optimal translation
-- statement:
--   Let $K\subseteq\mathbb R^n$ be compact, and let $K-w=\{y-w:y\in K\}$. For every $x,w\in\mathbb R^n$,
--
--   $$\phi_{K-w}^{**}(x)=\bigl(|x+w|^2-|x|^2\bigr)+\phi_K^{**}(x+w).$$
--
--   Moreover,
--
--   $$\bigl[\forall w,\ \phi_K^{**}(0)\le\phi_{K-w}^{**}(0)\bigr]
--   \quad\Longleftrightarrow\quad
--   \bigl[\forall x,\ \phi_K^{**}(0)\le\phi_K^{**}(x)\bigr].$$
--
--   The equivalence says that zero is an optimal translation exactly when the biconjugate is minimized at zero. Values are extended-real, so the identity includes points outside the closed convex hull and the empty compact set. Minimization at zero means the displayed universal comparison, also for the identically infinite empty-set function.
--
--   Differences from the source:
--   - encoding: Translations K−w and the extended-real convex biconjugate → The image under y ↦ y−w, with the exact finite norm-square correction added in EReal; minimization is a universal order comparison; reason: The formula retains every x and w, all infinite values and both directions of the minimization equivalence.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, p. 11, Lemma 2.3

import Definitions.Def_IsodiamVar_Simplex_Supplement_Legendre

open MeasureTheory

namespace IsodiamVar.Simplex.Supplement

/-- Lemma 2.3, p. 11: the complete translation identity and minimization equivalence. -/
theorem lemma_2_3 {n : ℕ} (K : Set (E n)) (hK : IsCompact K) :
    (∀ x w : E n,
      phiBiconjugate ((fun y : E n => y - w) '' K) x =
        (((‖x + w‖ ^ 2 - ‖x‖ ^ 2 : ℝ) : EReal) + phiBiconjugate K (x + w))) ∧
    ((∀ w : E n, phiBiconjugate K 0 ≤
        phiBiconjugate ((fun y : E n => y - w) '' K) 0) ↔
      ∀ x : E n, phiBiconjugate K 0 ≤ phiBiconjugate K x) := by sorry

end IsodiamVar.Simplex.Supplement
