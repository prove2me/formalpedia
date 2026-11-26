-- Prove2me | Theorems.Thm_MuirheadMST_measurable_latentRoots
-- name    : MuirheadMST.measurable_latentRoots
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T21:02:31.740675+00:00
-- url     : https://prove2.me/theorems/01deca1f-7a8b-4ee6-958c-f29a2fc2ca8a
-- title:
--   The ordered latent roots of a symmetric matrix are a measurable function of its entries
-- statement:
--   For every $m$, the map sending a real $m\times m$ array $A$ to its latent roots $l_1(A)\ge\cdots\ge l_m(A)$ (the eigenvalues in decreasing order when $A$ is symmetric, and $0$ otherwise) is Borel measurable.
--
--   This is needed for the law of the latent roots of a random symmetric matrix to be defined.
--
--   **Formalization Note** `latentRoots` is defined in `Definitions.Def_MuirheadMST_Wishart` through Mathlib's `Matrix.IsHermitian.eigenvalues₀`; arrays carry the product σ-algebra.
-- source:
--   R. J. Muirhead, Aspects of Multivariate Statistical Theory, Wiley, 1982, https://doi.org/10.1002/9780470316559, §3.2.5, Theorem 3.2.17, p. 104 (the latent-root density presupposes that the latent roots are measurable; Mathlib has no measurability or continuity result for `eigenvalues₀`)

import Mathlib
import Definitions.Def_MuirheadMST_Wishart

open MeasureTheory

namespace MuirheadMST

theorem measurable_latentRoots (m : ℕ) :
    Measurable (latentRoots : (Fin m → Fin m → ℝ) → Fin m → ℝ) := by sorry

end MuirheadMST
