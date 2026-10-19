-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_defect_rounding
-- name    : OAI.AsymptoticallyMinimalLittlewood.defect_rounding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:52:35.955223+00:00
-- url     : https://prove2.me/theorems/1603c4a5-01dc-47e2-b90f-b529deb8bcdd
-- title:
--   Rounding real coefficients in $[-1,1]$ to signs with uniform error $O\big(1+\sqrt{\mu\log(80N/\mu)}\big)$ on the unit circle
-- statement:
--   Let $N\ge 1$ and let $X=(X_0,\dots,X_{N-1})\in\mathbb{R}^{N}$ with $|X_k|\le 1$ for all $k$. For a real vector $v\in\mathbb{R}^{N}$ write $P_v(z)=\sum_{k=0}^{N-1}v_kz^{k}$, and define the defect mass of $X$ as
--   $$
--   \mu(X)=\frac12\sum_{k=0}^{N-1}\bigl(1-|X_k|\bigr).
--   $$
--   Then there are signs $\varepsilon_0,\dots,\varepsilon_{N-1}\in\{-1,1\}$ such that for every $z\in\mathbb{C}$ with $|z|=1$,
--
--   $$
--   \bigl|P_{\varepsilon}(z)-P_X(z)\bigr|\le 196608\Bigl(1+\sqrt{\mu(X)\log\frac{80N}{\mu(X)}}\Bigr).
--   $$
--
--   The theorem rounds a polynomial with real coefficients in $[-1,1]$ to a Littlewood polynomial (all coefficients $\pm 1$) with a uniform error on the unit circle controlled by how far the coefficients are from $\pm 1$, as measured by $\mu(X)$, rather than by the degree. For example, if $\mu(X)=\delta N$ the error is $O\bigl(1+\sqrt{\delta\log(80/\delta)}\,\sqrt N\bigr)$, which is small compared with $\sqrt N$ when $\delta$ is small. In the construction of flat Littlewood polynomials it converts a flat polynomial with real coefficients and nearly full energy into a flat polynomial with coefficients $\pm 1$.
--
--   **Formalization Note** $P_v(z)$ is `littlewoodValue v z`, the sign condition is `IsRealSigning ε` (each $\varepsilon_k$ is the real number $-1$ or $1$), and $\mu(X)$ is `defectMass X`. If $\mu(X)=0$, Lean's conventions $80N/0=0$ and $\log 0=0$ make the right-hand side equal to $196608$; in that case every $|X_k|=1$ and $\varepsilon=X$ has zero error.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L1225-L1361

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff
open scoped ComplexConjugate
open Finset

theorem OAI.AsymptoticallyMinimalLittlewood.defect_rounding {N : ℕ} (hN : 1 ≤ N) (X : Fin N → ℝ)
    (hX : ∀ k, |X k| ≤ 1) :
    ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ‖littlewoodValue ε z - littlewoodValue X z‖ ≤
          196608 * (1 + Real.sqrt (defectMass X * Real.log (80 * N / defectMass X))) := by sorry
