-- Prove2me | Theorems.Thm_GeomDL_Grids_shift_eigenvalues_distinct
-- name    : GeomDL.Grids.shift_eigenvalues_distinct
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:19.655452+00:00
-- url     : https://prove2.me/theorems/a5c95de9-3f05-470c-9edd-9a511154628a
-- title:
--   §4.2, side-note p. 37 — the eigenvalues e^{−2πik/n}, k = 0, …, n−1, of the shift S are distinct
-- statement:
--   Let $n \ge 1$. The eigenvalues $\lambda_k = e^{-2\pi i k/n}$ of the right shift $S$ on the Fourier basis vectors $\varphi_k$, $k = 0, 1, \dots, n-1$, are pairwise distinct: for $k, l \in \{0, \dots, n-1\}$,
--   $$e^{-2\pi i k/n} = e^{-2\pi i l/n} \;\Longrightarrow\; k = l .$$
--
--   The book needs distinct eigenvalues so that the common eigenbasis of the commuting circulant matrices is determined by the shift alone; it states that the assumption "is satisfied with our choice of $S$".
--
--   **Formalization Note** $k$ and $l$ are elements of `ZMod n`, entering the exponent through `ZMod.val`. Together with the eigenvector statement for $\varphi_k$ this says that $S$ has $n$ distinct eigenvalues.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.2, side-note p. 37, "We must additionally assume distinct eigenvalues … This assumption is satisfied with our choice of S."

import Mathlib
import Definitions.Def_GeomDL_Grids_Defs

open Matrix

namespace GeomDL.Grids
/-- Bronstein et al. §4.2, side-note p. 37: the shift `S` has distinct eigenvalues. The eigenvalues
`λ_k = e^{-2πik/n}`, `k = 0, …, n-1`, of `S` on the Fourier basis are pairwise distinct. -/
theorem shift_eigenvalues_distinct {n : ℕ} [NeZero n] (k l : ZMod n)
    (hkl : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ))) =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (l.val : ℂ) / (n : ℂ)))) :
    k = l := by sorry
end GeomDL.Grids
