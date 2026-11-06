-- Prove2me | Theorems.Thm_NewtonLCP_corollary_2_5
-- name    : NewtonLCP.corollary_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:28:42.589536+00:00
-- url     : https://prove2.me/theorems/c882000e-3a5b-4d54-8bd8-6d24ccddb64f
-- title:
--   Corollary 2.5 — $I_n+DMD$ is nonsingular for $M\in P_0$
-- statement:
--   For every $M\in P_0$ and every positive diagonal matrix $D$, the matrix
--
--   $$I_n+DMD$$
--
--   is nonsingular. Since $\mathcal P_\star\subseteq P_0$, this makes the Newton step (10) well defined for $\mathcal P_\star$-matrices, and justifies the singularity tests of Algorithm 3.
--
--   Differences from the source: none.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Corollary 2.5, p.7

import Mathlib
import Definitions.Def_NewtonLCP_MatrixClasses

open Matrix

namespace NewtonLCP

/-- **Corollary 2.5**. Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Corollary 2.5, p.7 (from Lemma 2.4, cited from [CPS09, Ch. 3]).

For any `M ∈ P₀` and positive diagonal `D`, the matrix `Iₙ + DMD` is nonsingular.

**Formalization Note.** `D = diag(d)`, `d > 0`; nonsingular means `det ≠ 0`. -/
theorem corollary_2_5 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : IsP0 M)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    (1 + diagonal d * M * diagonal d).det ≠ 0 := by sorry

end NewtonLCP
