-- Prove2me | Theorems.Thm_GoodViewsNotEnough_complete_scene_gram_matrix
-- name    : GoodViewsNotEnough.complete_scene_gram_matrix
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:53:30.168649+00:00
-- url     : https://prove2.me/theorems/a3925495-aeed-48e4-aad5-8ccb0929a8ad
-- title:
--   Lemma 7: complete scene Gram matrix
-- statement:
--   In the 512-dimensional model, let $r:\{1,\dots,513\}\to\mathbb{R}^{512}$ be a complete centred orthonormal basis of scene functions in $L^2(p)$, that is, $\mathbb{E}_p r=0$ and $\mathbb{E}_p rr^\top=I_{512}$. Then:
--
--   1. every scene-only encoder $h(S,U)=y(S)$ with $\mathbb{E}h=0$ and $\mathbb{E}hh^\top=I_{512}$ has the form $h=Qr(S)$ for some $Q\in O(512)$;
--   2. the Gram matrix of $r$ is
--   $$r(s)^\top r(s')=\frac{\mathbf 1_{s=s'}}{p_s}-1;$$
--   3. $\|r(s)\|^2=3$ on the two common scenes and $\|r(s)\|^2=1021$ on the other scenes;
--   4. for distinct scenes, $\|r(s)-r(s')\|^2$ is $8$ (common/common), $1026$ (common/other) and $2044$ (other/other).
--
--   So the whole scene-only whitened class is one rotation orbit, and the direction-averaged Epps–Pulley value is the same throughout it.
-- source:
--   Anran Xu, Good Views Are Not Enough: Global Counterexamples for Gaussian-Regularized JEPAs, arXiv:2611.12137v1 (2026), Appendix D.3, Lemma 7, eqs. (16)-(17), p. 18

import Mathlib
import Definitions.Def_GoodViewsNotEnough_Basic

open MeasureTheory Complex

namespace GoodViewsNotEnough

theorem complete_scene_gram_matrix (r : Fin 513 → Fin 512 → ℝ) (hr : IsCenteredOrthonormalBasis r) :
    (∀ h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ, (∀ s U U', h s U = h s U') → IsWhitenedHD h →
      ∃ Q ∈ Matrix.orthogonalGroup (Fin 512) ℝ, ∀ s U, h s U = Q.mulVec (r s)) ∧
    (∀ s s', ∑ a, r s a * r s' a = (if s = s' then 1 / hdSceneProb s else 0) - 1) ∧
    (∀ s : Fin 513, (s : ℕ) < 2 → ∑ a, r s a ^ 2 = 3) ∧
    (∀ s : Fin 513, 2 ≤ (s : ℕ) → ∑ a, r s a ^ 2 = 1021) ∧
    (∀ s s' : Fin 513, s ≠ s' → (s : ℕ) < 2 → (s' : ℕ) < 2 → ∑ a, (r s a - r s' a) ^ 2 = 8) ∧
    (∀ s s' : Fin 513, (s : ℕ) < 2 → 2 ≤ (s' : ℕ) → ∑ a, (r s a - r s' a) ^ 2 = 1026) ∧
    (∀ s s' : Fin 513, s ≠ s' → 2 ≤ (s : ℕ) → 2 ≤ (s' : ℕ) → ∑ a, (r s a - r s' a) ^ 2 = 2044) := by sorry

end GoodViewsNotEnough
