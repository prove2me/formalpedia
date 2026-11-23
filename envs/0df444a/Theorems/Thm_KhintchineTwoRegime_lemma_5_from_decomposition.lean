-- Prove2me | Theorems.Thm_KhintchineTwoRegime_lemma_5_from_decomposition
-- name    : KhintchineTwoRegime.lemma_5_from_decomposition
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:48:26.10664+00:00
-- url     : https://prove2.me/theorems/4174218d-bbc7-4775-b063-d7826fc4c00b
-- title:
--   Lemma 5 lower estimate from the four-coordinate decomposition
-- statement:
--   Let $n\ge4$ and let $\omega\in\mathbb R^n$ be a proper unit vector. Put $q=\omega_1+\omega_2$ and $x=q-\omega_3-\omega_4$. Then
--   $$
--   K_n(\omega)\ge\Phi_q(x)
--    =\frac34q-\frac38x+\frac1{8\sqrt2}
--      \left(\sqrt{1-q^2+qx}+2\sqrt{1-q^2+qx-x^2}\right).
--   $$
--
--   This is the probabilistic and geometric step of Lemma 5, before its separate derivative assertions. Its proof uses Lemma 4, Szarek's sharp Khintchine inequality, and the tail-norm identities (14).
--
--   **Formalization Note** The dimension is written $n=m+4$, so all four leading coordinates exist without padding. `IsProper` supplies exactly the monotonicity, nonnegativity, and unit-norm hypotheses used by the source.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2, Lemma 5, p.7; eq. (14), p.7; Appendix A.6, pp.15–16 (equations (23) and the two radicand inequalities).

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_IsProper
import Definitions.Def_KhintchineTwoRegime_Phi

theorem KhintchineTwoRegime.lemma_5_from_decomposition (m : ℕ) (ω : Fin (m + 4) → ℝ)
    (hω : KhintchineTwoRegime.IsProper ω) :
    KhintchineTwoRegime.Phi (ω ⟨0, by omega⟩ + ω ⟨1, by omega⟩)
      (ω ⟨0, by omega⟩ + ω ⟨1, by omega⟩ - ω ⟨2, by omega⟩ - ω ⟨3, by omega⟩) ≤
        KhintchineTwoRegime.K (m + 4) ω := by sorry
