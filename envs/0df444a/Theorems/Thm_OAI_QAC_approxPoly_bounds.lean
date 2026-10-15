-- Prove2me | Theorems.Thm_OAI_QAC_approxPoly_bounds
-- name    : OAI.QAC.approxPoly_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:41:56.935141+00:00
-- url     : https://prove2.me/theorems/1a132429-ce52-4f2d-9fe2-5b5f1d54c0ae
-- title:
--   Degree, weight, normalization and decay of the Chebyshev approximant to the indicator of zero
-- statement:
--   For $r,m,k\in\mathbb N$ let $T_k$ be the Chebyshev polynomial of the first kind of degree $k$ and set
--   $$\rho_r(X)=\prod_{j=1}^r\Bigl(1-\frac Xj\Bigr),\qquad \ell_{r,m}(X)=\frac{m+r}{m-r}-\frac{2}{m-r}X,\qquad q_{r,m,k}=\Bigl(T_k\Bigl(\frac{m+r}{m-r}\Bigr)\Bigr)^{-1}\rho_r\cdot\bigl(T_k\circ\ell_{r,m}\bigr).$$
--   For $R\in\mathbb R$ let $\|p\|_R=\sum_k|c_k|R^k$ be the weight of a real polynomial $p=\sum_kc_kX^k$.
--
--   Let $R\ge0$ and let $r,m,k\in\mathbb N$ satisfy $r\ge1$, $2r\le m$ and $4r\log m\le k\sqrt{r/m}$. Then:
--
--   1. $\deg q_{r,m,k}\le r+k$;
--   2. $\|q_{r,m,k}\|_R\le(1+R)^r\,(7+4R)^k$;
--   3. $q_{r,m,k}(0)=1$;
--   4. for every integer $x$ with $1\le x\le m$,
--   $$
--   |q_{r,m,k}(x)|\le2\,e^{-3r\log m}=2\,m^{-3r}.
--   $$
--
--   Thus $q_{r,m,k}$ approximates the indicator function of $\{0\}$ on $\{0,1,\dots,m\}$: it equals $1$ at $0$ and is polynomially small in $m$ at $1,\dots,m$, while its degree and weight stay controlled. Evaluated at the mismatch operator of a count, it approximates the zero-mismatch projection in the polynomial step of the localization argument.
--
--   **Formalization Note** The polynomial is `approxPoly r m k`, built from `rootPoly r` and `scalePoly r m`; the degree is `natDegree`, and $\log m$ is `Real.log` of $m$ cast to a real number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Polynomial.lean#L270-L340

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

theorem OAI.QAC.approxPoly_bounds {r m k : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hr : 1 ≤ r) (hm : 2 * r ≤ m)
    (hk : 4 * (r : ℝ) * Real.log m ≤ (k : ℝ) * Real.sqrt ((r : ℝ) / m)) :
    (approxPoly r m k).natDegree ≤ r + k ∧
    weight R (approxPoly r m k) ≤ (1 + R) ^ r * (7 + 4 * R) ^ k ∧
    (approxPoly r m k).eval 0 = 1 ∧
    ∀ x : ℕ, 1 ≤ x → x ≤ m →
      |(approxPoly r m k).eval (x : ℝ)| ≤ 2 * Real.exp (-(3 * (r : ℝ) * Real.log m)) := by sorry
