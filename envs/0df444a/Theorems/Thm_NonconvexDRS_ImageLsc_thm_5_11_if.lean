-- Prove2me | Theorems.Thm_NonconvexDRS_ImageLsc_thm_5_11_if
-- name    : NonconvexDRS.ImageLsc.thm_5_11_if
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:37.356263+00:00
-- url     : https://prove2.me/theorems/3eeec659-abdb-4afd-95be-4d4e476f879f
-- title:
--   Proof of Theorem 5.11, p. 24 — the "if" direction: (5.5) on dom g makes (Bg) lsc at every point of B dom g
-- statement:
--   Let $g:\mathbb R^n\to\overline{\mathbb R}$ be lower semicontinuous (with values in $\mathbb R\cup\{+\infty\}$) and let $B\in\mathbb R^{p\times n}$. Suppose that condition (5.5) holds at every $\bar z\in\operatorname{dom}g$:
--   $$\liminf_{\substack{\|d\|\to\infty\\ Bd\to0}} g(\bar z+d)\;\ge\;\inf_{d\in\ker B} g(\bar z+d)\qquad\forall\bar z\in\operatorname{dom}g.$$
--   Then the image function $(Bg)(s)=\inf\{g(z)\mid Bz=s\}$ is lower semicontinuous at every point $\bar s\in B\operatorname{dom}g=\operatorname{dom}(Bg)$.
--
--   Verbatim (p. 24): "Suppose now that (5.5) holds, and given $\bar s\in\operatorname{dom}(Bg)$ consider a sequence $(s_k)_{k\in\mathbb N}\subseteq\operatorname{lev}_{\le\alpha}(Bg)$ for some $\alpha\in\mathbb R$ and such that $s_k\to\bar s$. Then, it suffices to show that $\bar s\in\operatorname{lev}_{\le\alpha}(Bg)$."
--
--   This is the sufficiency half of Theorem 5.11, exactly in the range the proof covers.
--
--   **Formalization Note** The conclusion is lower semicontinuity at the points of $B\operatorname{dom}g$ only, which is what the proof shows ("given $\bar s\in\operatorname{dom}(Bg)$"). Lower semicontinuity at every point of $\mathbb R^p$ does not follow: for $g$ the indicator of the closed set $\{(x,y):x>0,\ xy\ge1\}$ and $B=[1\ 0]$, condition (5.5) holds at every $\bar z\in\operatorname{dom}g$, yet $(Bg)(s)=0$ for $s>0$ and $+\infty$ for $s\le0$, so $(Bg)$ is not lsc at $0\notin B\operatorname{dom}g$. Lower semicontinuity at a point is the neighbourhood form ($y<(Bg)(\bar s)$ implies $y<(Bg)(s)$ for all $s$ near $\bar s$), equivalent to the sequential level-set form of the page.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 24, proof of Theorem 5.11, "if" direction

import Mathlib
import Definitions.Def_NonconvexDRS_ImageLsc_Setting

namespace NonconvexDRS.ImageLsc

theorem thm_5_11_if {n p : ℕ} (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hbot : ∀ z, g z ≠ ⊥) (hlsc : LowerSemicontinuous g)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (h55 : ∀ zbar ∈ dom g, Cond55 g B zbar) :
    ∀ sbar ∈ B '' dom g, LowerSemicontinuousAt (NonconvexDRS.ADMM.imageFn B g) sbar := by sorry

end NonconvexDRS.ImageLsc
