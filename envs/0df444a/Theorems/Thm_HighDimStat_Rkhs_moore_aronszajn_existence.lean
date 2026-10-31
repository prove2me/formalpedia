-- Prove2me | Theorems.Thm_HighDimStat_Rkhs_moore_aronszajn_existence
-- name    : HighDimStat.Rkhs.moore_aronszajn_existence
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T01:50:10.113668+00:00
-- url     : https://prove2.me/theorems/5cba191d-97be-4c7b-ae9a-46d5f1c3d9bf
-- title:
--   Existence half of the Moore-Aronszajn theorem
-- statement:
--   For any positive semidefinite kernel $K : X \times X \to \mathbb{R}$, completing the pre-Hilbert space of finite linear combinations of kernel sections $K(\cdot, x)$ yields a Hilbert space $H$ with linear embedding $\mathrm{toFun} : H \to (X \to \mathbb{R})$ and feature map $\Phi : X \to H$ satisfying $\mathrm{IsRKHS}\,K\,\mathrm{toFun}\,\Phi$.

import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core

namespace HighDimStat.Rkhs

/-- **Existence half of the Moore-Aronszajn theorem (Wainwright Theorem 12.11, p. 389).**
For any positive semidefinite kernel `K` on `X`, completing the pre-Hilbert space of finite linear
combinations of kernel sections `K(·, x)` yields a Hilbert space `H` with linear embedding `toFun`
and feature map `feature` satisfying `IsRKHS K toFun feature`. -/
theorem moore_aronszajn_existence {X : Type*} (K : X → X → ℝ) (hK : IsPSDKernel K) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (toFun : H →ₗ[ℝ] (X → ℝ)) (feature : X → H), IsRKHS K toFun feature := by sorry

end HighDimStat.Rkhs
