-- Prove2me | Theorems.Thm_NAGFlow_GSSpectrum_eq_124
-- name    : NAGFlow.GSSpectrum.eq_124
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:51.226983+00:00
-- url     : https://prove2.me/theorems/05434455-97f8-45f4-a8cd-a367da2f141b
-- title:
--   (124), p. 35 — E(α, R) = (1/δ)(1 + dα, cα(1 + dα); −bα, 1 + aα − bcα²) and 0 < det E(α, R) = 1/δ = 1/(1 + |tr R|α + adα²) < 1
-- statement:
--   Let $a,b,c,d\ge 0$ and
--   $$R=\begin{pmatrix}-a & c\\ -b & -d\end{pmatrix}$$
--   with $\operatorname{tr}R<0<\det R$. Split $R=M+N$ with $M=\begin{pmatrix}-a&0\\-b&-d\end{pmatrix}$ its lower triangular part and $N=\begin{pmatrix}0&c\\0&0\end{pmatrix}$. For every step size $\alpha>0$, with $\delta=(1+a\alpha)(1+d\alpha)$,
--   $$E(\alpha,R):=(I-\alpha M)^{-1}(I+\alpha N)=\frac1\delta\begin{pmatrix}1+d\alpha & c\alpha(1+d\alpha)\\ -b\alpha & 1+a\alpha-bc\alpha^2\end{pmatrix},$$
--   and
--   $$0<\det E(\alpha,R)=\frac1\delta=\frac{1}{1+|\operatorname{tr}R|\,\alpha+ad\alpha^2}<1.$$
--
--   This is the explicit form of the Gauss–Seidel step for the scalar model, from which Lemma A.1 and the spectral bounds for $G_{\mathrm{HB}}$ and $G_{\mathrm{NAG}}$ are derived.
--
--   **Formalization Note.** The paper leaves $\alpha>0$ implicit (it is the step size of (41)); it is a hypothesis here. $M$ and $N$ are obtained from $R$ by the lower-triangular split of the definitions file, which on this $R$ gives exactly the printed matrices.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, App. A, proof of Theorem 2.1, (124) and the display after it, p. 35

import Mathlib
import Definitions.Def_NAGFlow_GSSpectrum_Setting

namespace NAGFlow.GSSpectrum

open Matrix

/-- (124) and the display after it, App. A, p. 35. For R = (−a c ; −b −d) with a, b, c, d ≥ 0 and
tr R < 0 < det R, and a step size α > 0, the Gauss–Seidel matrix E(α, R) = (I − αM)⁻¹(I + αN)
(M the lower triangular part of R, N = R − M) equals
(1/δ)(1 + dα, cα(1 + dα) ; −bα, 1 + aα − bcα²) with δ = (1 + aα)(1 + dα), and
0 < det E(α, R) = 1/δ = 1/(1 + |tr R|α + adα²) < 1. -/
theorem eq_124 (a b c d α : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (htr : (Rmat a b c d).trace < 0) (hdet : 0 < (Rmat a b c d).det) (hα : 0 < α) :
    ER α (Rmat a b c d) = (1 / ((1 + a * α) * (1 + d * α))) •
        !![1 + d * α, c * α * (1 + d * α); -(b * α), 1 + a * α - b * c * α ^ 2] ∧
      0 < (ER α (Rmat a b c d)).det ∧
      (ER α (Rmat a b c d)).det = 1 / ((1 + a * α) * (1 + d * α)) ∧
      1 / ((1 + a * α) * (1 + d * α)) = 1 / (1 + |(Rmat a b c d).trace| * α + a * d * α ^ 2) ∧
      1 / (1 + |(Rmat a b c d).trace| * α + a * d * α ^ 2) < 1 := by sorry

end NAGFlow.GSSpectrum
