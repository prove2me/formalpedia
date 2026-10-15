-- Prove2me | Theorems.Thm_OAI_QAC_chebyshev_denominator
-- name    : OAI.QAC.chebyshev_denominator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:41:14.800795+00:00
-- url     : https://prove2.me/theorems/06678e25-0482-4ef0-83d8-746cf1609f84
-- title:
--   Lower bounds for the Chebyshev value $T_k\bigl(\frac{m+r}{m-r}\bigr)$
-- statement:
--   Let $T_k$ be the Chebyshev polynomial of the first kind of degree $k\in\mathbb N$, so that $T_k(\cos\theta)=\cos k\theta$, and let $m,r$ be real numbers with $0<r<m$. Then
--   $$
--   1\le T_k\Bigl(\frac{m+r}{m-r}\Bigr)\qquad\text{and}\qquad \frac{1}{2}\,e^{k\sqrt{r/m}}\le T_k\Bigl(\frac{m+r}{m-r}\Bigr).
--   $$
--
--   Outside $[-1,1]$ Chebyshev polynomials grow exponentially in the degree, and this quantifies the growth at the point $\frac{m+r}{m-r}>1$, which is the image of $0$ under the affine map sending $r\mapsto1$ and $m\mapsto-1$. This value is the normalizing denominator of the polynomial that approximates the indicator of $0$, and the lower bound is what makes that polynomial small on $[r,m]$ while it equals $1$ at $0$.
--
--   **Formalization Note** $T_k$ is `Polynomial.Chebyshev.T ℝ k` evaluated at a real number, and the square root is `Real.sqrt`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Polynomial.lean#L120-L159

import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

theorem OAI.QAC.chebyshev_denominator (k : ℕ) {m r : ℝ} (hr : 0 < r) (hm : r < m) :
    1 ≤ (Polynomial.Chebyshev.T ℝ k).eval ((m + r) / (m - r)) ∧
    Real.exp ((k : ℝ) * Real.sqrt (r / m)) / 2 ≤
      (Polynomial.Chebyshev.T ℝ k).eval ((m + r) / (m - r)) := by sorry
