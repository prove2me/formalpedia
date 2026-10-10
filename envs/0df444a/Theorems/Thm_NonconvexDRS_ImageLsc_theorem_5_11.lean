-- Prove2me | Theorems.Thm_NonconvexDRS_ImageLsc_theorem_5_11
-- name    : NonconvexDRS.ImageLsc.theorem_5_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:08.74239+00:00
-- url     : https://prove2.me/theorems/ba4478ec-63e8-475d-b6f7-ed34baf7b894
-- title:
--   Theorem 5.11, p. 24 (corrected) — for lsc g, the image function (Bg) is lsc at every point of B dom g iff (5.5) holds on dom g
-- statement:
--   Let $g:\mathbb R^n\to\overline{\mathbb R}=\mathbb R\cup\{+\infty\}$ be lower semicontinuous, let $B\in\mathbb R^{p\times n}$, and let $(Bg)(s)=\inf\{g(z)\mid Bz=s\}$ be the image function of Definition 5.1. Then $(Bg)$ is lower semicontinuous at every point of $B\operatorname{dom}g=\operatorname{dom}(Bg)$ if and only if
--   $$\liminf_{\substack{\|d\|\to\infty\\ Bd\to0}} g(\bar z+d)\;\ge\;\inf_{d\in\ker B} g(\bar z+d)\qquad\forall\bar z\in\operatorname{dom}g.\tag{5.5}$$
--
--   Verbatim (p. 24): "Theorem 5.11. For any lsc function $g:\mathbb R^n\to\overline{\mathbb R}$ and $B\in\mathbb R^{p\times n}$, the image function $(Bg)$ is lsc iff $\liminf_{\|d\|\to\infty,\,Bd\to0}g(\bar z+d)\ge\inf_{d\in\ker B}g(\bar z+d)$ $\forall\bar z\in\operatorname{dom}g$. (5.5) In particular, for any lsc and level bounded function $g:\mathbb R^n\to\overline{\mathbb R}$ and $B\in\mathbb R^{p\times n}$, $(Bg)$ is lsc."
--
--   The theorem characterizes when the image function inherits lower semicontinuity from $g$: failures can only come from the behaviour of $g$ at infinity along directions that $B$ nearly annihilates. In the paper it supplies sufficient conditions for Assumption IIa4, the lower semicontinuity of $\varphi_2=(Bg)$ in the DRS reformulation of ADMM.
--
--   **Formalization Note** The statement is corrected: lower semicontinuity of $(Bg)$ is asserted at the points of $B\operatorname{dom}g$, not everywhere. As printed, the "if" direction is false: for $n=2$, $p=1$, $B=[1\ 0]$ and $g$ the indicator of the closed set $\{(x,y):x>0,\ xy\ge1\}$, condition (5.5) holds at every $\bar z\in\operatorname{dom}g$ (its right side is $0$ and $g\ge0$), but $(Bg)(s)=0$ for $s>0$ and $+\infty$ for $s\le0$, so $(Bg)$ is not lsc at $0$. The proof's "given $\bar s\in\operatorname{dom}(Bg)$" covers exactly $B\operatorname{dom}g$, and both directions of the proof establish the corrected equivalence. The "In particular" sentence is true as printed and is a separate item. Properness of $g$ is not assumed (if $\operatorname{dom}g=\emptyset$ both sides hold trivially). $\overline{\mathbb R}$ is `EReal` with $g$ never $-\infty$; $(Bg)$ is an `EReal` infimum. The liminf is along the filter of $d$ with $\|d\|\to\infty$ and $Bd\to0$; when that filter is trivial (e.g. $B$ injective) the liminf is $+\infty$, the paper's reading of an empty liminf.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 24, Theorem 5.11 and (5.5), corrected (lsc on B dom g)

import Mathlib
import Definitions.Def_NonconvexDRS_ImageLsc_Setting

namespace NonconvexDRS.ImageLsc

theorem theorem_5_11 {n p : ℕ} (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hbot : ∀ z, g z ≠ ⊥) (hlsc : LowerSemicontinuous g)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
    (∀ sbar ∈ B '' dom g, LowerSemicontinuousAt (NonconvexDRS.ADMM.imageFn B g) sbar) ↔
      ∀ zbar ∈ dom g, Cond55 g B zbar := by sorry

end NonconvexDRS.ImageLsc
