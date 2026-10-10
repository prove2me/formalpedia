-- Prove2me | Theorems.Thm_NonconvexDRS_ImageLsc_thm_5_11_only_if
-- name    : NonconvexDRS.ImageLsc.thm_5_11_only_if
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:29:23.912423+00:00
-- url     : https://prove2.me/theorems/72f44b65-457c-466b-97f0-9daa3efd2a82
-- title:
--   Proof of Theorem 5.11, p. 24 — the "only if" direction: lsc of (Bg) on B dom g forces (5.5) on dom g
-- statement:
--   Let $g:\mathbb R^n\to\overline{\mathbb R}$ be lower semicontinuous (with values in $\mathbb R\cup\{+\infty\}$) and let $B\in\mathbb R^{p\times n}$. Suppose that the image function $(Bg)(s)=\inf\{g(z)\mid Bz=s\}$ is lower semicontinuous at every point of $B\operatorname{dom}g$. Then condition (5.5) holds at every $\bar z\in\operatorname{dom}g$:
--   $$\liminf_{\substack{\|d\|\to\infty\\ Bd\to0}} g(\bar z+d)\;\ge\;\inf_{d\in\ker B} g(\bar z+d).$$
--
--   Verbatim (p. 24): "To show the converse implication, suppose that (5.5) does not hold. Thus, there exist $\bar z\in\operatorname{dom}g$ and $(d^k)_{k\in\mathbb N}\subset\mathbb R^n$ such that $Bd^k\to0$ as $k\to\infty$, and such that, for some $\varepsilon>0$, $g(\bar z+d^k)+\varepsilon\le\inf_{d\in\ker B}g(\bar z+d)=(Bg)(B\bar z)$ $\forall k$. Then, $s_k:=B(\bar z+d^k)$ satisfies $s_k\to B\bar z$ as $k\to\infty$, and $(Bg)(B\bar z)\ge\liminf_{k\to\infty}g(\bar z+d^k)+\varepsilon\ge\liminf_{k\to\infty}(Bg)(s^k)+\varepsilon$, hence $(Bg)$ is not lsc at $B\bar z$."
--
--   This is the necessity half of Theorem 5.11. The proof exhibits a failure of lower semicontinuity at $B\bar z$, a point of $B\operatorname{dom}g$, so lower semicontinuity there is all that is assumed.
--
--   **Formalization Note** The hypothesis is lower semicontinuity of $(Bg)$ at the points of $B\operatorname{dom}g$, weaker than global lower semicontinuity, so this statement implies the printed "only if". The liminf is taken along the filter of $d$ with $\|d\|\to\infty$ and $Bd\to0$; when that filter is trivial the liminf is $+\infty$.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 24, proof of Theorem 5.11, converse implication

import Mathlib
import Definitions.Def_NonconvexDRS_ImageLsc_Setting

namespace NonconvexDRS.ImageLsc

theorem thm_5_11_only_if {n p : ℕ} (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hbot : ∀ z, g z ≠ ⊥) (hlsc : LowerSemicontinuous g)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (hBg : ∀ sbar ∈ B '' dom g, LowerSemicontinuousAt (NonconvexDRS.ADMM.imageFn B g) sbar) :
    ∀ zbar ∈ dom g, Cond55 g B zbar := by sorry

end NonconvexDRS.ImageLsc
