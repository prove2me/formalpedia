-- Prove2me | Theorems.Thm_HighDimStat_Rkhs_moore_aronszajn_existence_v2
-- name    : HighDimStat.Rkhs.moore_aronszajn_existence_v2
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T03:00:45.282776+00:00
-- url     : https://prove2.me/theorems/7c0ee17a-da80-491f-ae5c-1e5d6606c512
-- title:
--   Existence half of the Moore-Aronszajn theorem (Type 0)
-- statement:
--   For any positive semidefinite kernel $K : X \times X \to \mathbb{R}$ on a type $X : \mathrm{Type}$, completing the pre-Hilbert space of finite linear combinations of kernel sections $K(\cdot, x)$ yields a real Hilbert space $H : \mathrm{Type}$ with linear embedding $\mathrm{toFun} : H \to_{\mathbb{R}} (X \to \mathbb{R})$ and feature map $\mathrm{feature} : X \to H$ satisfying $\mathrm{IsRKHS}\;K\;\mathrm{toFun}\;\mathrm{feature}$ (repaired universe binder `{X : Type}` matching `H : Type`).

import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core

namespace HighDimStat.Rkhs

/-- **Existence half of the Moore-Aronszajn theorem (Wainwright Theorem 12.11, p. 389).**
For any positive semidefinite kernel `K` on `X : Type`, completing the pre-Hilbert space of finite
linear combinations of kernel sections `K(·, x)` yields a Hilbert space `H : Type` with linear
embedding `toFun` and feature map `feature` satisfying `IsRKHS K toFun feature`. -/
theorem moore_aronszajn_existence_v2 {X : Type} (K : X → X → ℝ) (hK : IsPSDKernel K) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (toFun : H →ₗ[ℝ] (X → ℝ)) (feature : X → H), IsRKHS K toFun feature := by sorry

end HighDimStat.Rkhs
