-- Prove2me | Theorems.Thm_MIBF_Balanced_theorem_4_6
-- name    : MIBF.Balanced.theorem_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:58:52.96048+00:00
-- url     : https://prove2.me/theorems/724a2cc8-2fe4-4b89-bc62-ad2d8f4ff3b1
-- title:
--   Theorem 4.6 — global contact-plane inequality: $Q_c\ge0$ on $[0,1]^2$, with equality exactly at $(0,0)$, $(a,b)$, $(1,1)$
-- statement:
--   Natural logarithms; $h$ is the binary entropy in nats and $j$ the extended Jeffreys cost in nats ($j(0,0)=j(1,1)=0$, $j=+\infty$ at the other boundary points). Let $0<a<b<1$, put $d=b-a$, and let $A,D$ solve the linear system
--   $$\begin{pmatrix}-\ln a & -\ln b\\ -\ln(1-a) & -\ln(1-b)\end{pmatrix}\begin{pmatrix}A\\ D\end{pmatrix}=\begin{pmatrix}d^2/(2ab)\\ d^2/[2(1-a)(1-b)]\end{pmatrix}. \qquad (24)$$
--   Assume $A\ge0$ and $D\ge0$, and define
--   $$c=\frac{j(a,b)+A\,h(a)+D\,h(b)}{b-a}.$$
--   Then $A+D>0$, $c>0$, and
--   $$Q_c(x,y)=j(x,y)-c\,(y-x)+A\,h(x)+D\,h(y)\ \ge\ 0\qquad (x,y\in[0,1]),$$
--   with equality exactly at $(x,y)\in\{(0,0),(a,b),(1,1)\}$.
--
--   Geometrically, a plane in $(x,y,h(x),h(y))$ touches the cost at the two diagonal corners and the interior anchor $(a,b)$ and lies below it on the whole closed square. Integrated against a law with prescribed means and mean entropies, it produces the contact-plane lower bounds on the edge value (Theorem 4.8 and Proposition 4.9).
--
--   **Formalization Note** $A$ and $D$ are real variables constrained by the two equations of (24); the coefficient matrix is invertible for $0<a<b<1$ (p. 13), so they are the unique solution. $Q_c$ is `contactGap A D c x y`, extended-real valued, equal to $+\infty$ where $j=+\infty$.
--
--   Differences from the source:
--   - encoding: "let $A,D$ solve (24)" → $A,D$ variables with the two equations of (24) as hypotheses; reason: the matrix is invertible, so these hypotheses determine $A,D$ uniquely; no division is hidden.
--   - encoding: $Q_c$ with the extended cost on $[0,1]^2$ → extended-real `contactGap`, $+\infty$ off the two diagonal corners on the boundary; reason: the boundary convention of (5).
--   - reading: the parenthetical "the inhomogeneous system automatically gives $A+D>0$" and "$c=\dots>0$" → stated as the conclusions $0<A+D$ and $0<c$; reason: they are claims of the theorem's statement.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), p. 12, Theorem 4.6, eqs. (24)–(25); proof in Appendix C

import Mathlib
import Definitions.Def_MIBF_Balanced_EdgeValue
import Definitions.Def_MIBF_Balanced_ContactPlane

namespace MIBF.Balanced
theorem theorem_4_6 (a b A D : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (h24_1 : -Real.log a * A + -Real.log b * D = (b - a) ^ 2 / (2 * a * b))
    (h24_2 : -Real.log (1 - a) * A + -Real.log (1 - b) * D
      = (b - a) ^ 2 / (2 * (1 - a) * (1 - b)))
    (hA : 0 ≤ A) (hD : 0 ≤ D) :
    let c := (natInteriorCost a b + A * Real.binEntropy a + D * Real.binEntropy b) / (b - a)
    0 < A + D ∧ 0 < c ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ contactGap A D c x y) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        (contactGap A D c x y = 0 ↔
          (x = 0 ∧ y = 0) ∨ (x = a ∧ y = b) ∨ (x = 1 ∧ y = 1))) := by sorry
end MIBF.Balanced
