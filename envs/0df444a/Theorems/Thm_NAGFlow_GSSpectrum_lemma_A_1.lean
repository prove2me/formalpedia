-- Prove2me | Theorems.Thm_NAGFlow_GSSpectrum_lemma_A_1
-- name    : NAGFlow.GSSpectrum.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:38.887784+00:00
-- url     : https://prove2.me/theorems/a0d71a4b-a7fe-4b73-a525-766030f62c25
-- title:
--   Lemma A.1, pp. 35–36 — if |tr R| − 2√(det R) ≤ bcα ≤ |tr R| + 2√(det R), then ρ(E(α, R)) = 1/√(1 + |tr R|α + adα²) < 1
-- statement:
--   Let $a,b,c,d\ge0$ and $R=\begin{pmatrix}-a & c\\ -b & -d\end{pmatrix}$ with $\operatorname{tr}R<0<\det R$, and let $E(\alpha,R)$ be the Gauss–Seidel matrix of (124). If $\alpha>0$ satisfies
--   $$|\operatorname{tr}R|-2\sqrt{\det R}\;\le\; bc\,\alpha\;\le\;|\operatorname{tr}R|+2\sqrt{\det R},\tag{126}$$
--   then
--   $$\rho(E(\alpha,R))=\frac{1}{\sqrt{1+|\operatorname{tr}R|\,\alpha+ad\alpha^2}}<1,$$
--   and in fact every eigenvalue $\theta$ of $E(\alpha,R)$ satisfies $|\theta|=1/\sqrt{1+|\operatorname{tr}R|\,\alpha+ad\alpha^2}$.
--
--   Condition (126) is exactly the condition under which the eigenvalues of $E(\alpha,R)$ form a complex-conjugate pair (or a double real root), so that both lie on the circle $|\theta|=\sqrt{\det E(\alpha,R)}$. The lemma is the scalar building block of Theorem 2.1.
--
--   **Formalization Note.** Eigenvalues are complex. "$\rho=\ldots$" is stated as: the value is the greatest modulus of an eigenvalue; the stronger clause that every eigenvalue has this modulus is the statement made in the lemma's proof ("any solution to (125) satisfies $|\theta|=\sqrt{\det E(\alpha,R)}$").
-- source:
--   Luo & Chen, arXiv:1909.03145v4, Lemma A.1 and (126), pp. 35–36

import Mathlib
import Definitions.Def_NAGFlow_GSSpectrum_Setting

namespace NAGFlow.GSSpectrum

open Matrix

/-- Lemma A.1, pp. 35–36. Let R = (−a c ; −b −d) with a, b, c, d ≥ 0 and tr R < 0 < det R, and
E(α, R) as in (124). If α > 0 satisfies (126),
|tr R| − 2√(det R) ≤ bcα ≤ |tr R| + 2√(det R), then ρ(E(α, R)) = 1/√(1 + |tr R|α + adα²) < 1;
moreover every eigenvalue of E(α, R) has exactly this modulus. -/
theorem lemma_A_1 (a b c d α : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (htr : (Rmat a b c d).trace < 0) (hdet : 0 < (Rmat a b c d).det) (hα : 0 < α)
    (h126l : |(Rmat a b c d).trace| - 2 * Real.sqrt (Rmat a b c d).det ≤ b * c * α)
    (h126u : b * c * α ≤ |(Rmat a b c d).trace| + 2 * Real.sqrt (Rmat a b c d).det) :
    IsSpecRadius (ER α (Rmat a b c d))
        (1 / Real.sqrt (1 + |(Rmat a b c d).trace| * α + a * d * α ^ 2)) ∧
      (∀ θ ∈ cspec (ER α (Rmat a b c d)),
        ‖θ‖ = 1 / Real.sqrt (1 + |(Rmat a b c d).trace| * α + a * d * α ^ 2)) ∧
      1 / Real.sqrt (1 + |(Rmat a b c d).trace| * α + a * d * α ^ 2) < 1 := by sorry

end NAGFlow.GSSpectrum
