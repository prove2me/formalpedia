-- Prove2me | Theorems.Thm_JRCurvedQFT_Symmetries_theorem_6_2
-- name    : JRCurvedQFT.Symmetries.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:03:00.596298+00:00
-- url     : https://prove2.me/theorems/fef5d0d3-3b8b-40e7-827d-3b4ddc686940
-- title:
--   Theorem 6.2 (Klein–Landau, Fröhlich) — unique self-adjoint generator of a symmetric local semigroup
-- statement:
--   Let $(S_\alpha,\mathscr D_\alpha,T)$ be a symmetric local semigroup on a complex Hilbert space $\mathcal H$. There exists a unique self-adjoint operator $A$ such that
--   $$\mathscr D_\alpha\subset D(e^{-\alpha A})\quad\text{and}\quad S_\alpha=e^{-\alpha A}|_{\mathscr D_\alpha}\qquad\text{for all }\alpha\in[0,T].$$
--   Moreover, for every real $c$, $A\ge-c$ if and only if $\|S_\alpha f\|\le e^{c\alpha}\|f\|$ for all $f\in\mathscr D_\alpha$ and $0<\alpha<T$.
--
--   This is the result that makes a generator available even though no single domain $\mathscr D_\alpha$ is dense; it is the analytic input of the reflected case of Theorem 6.4.
--
--   Differences from the source:
--   - reading: (ii) α → S_α is weakly continuous → for f ∈ D_β and g ∈ H, α ↦ ⟪g, S_α f⟫ is continuous on [0, β]; reason: S_α f is defined only while f ∈ D_α; this is the interval on which the condition can be stated
--   - encoding: e^{−αA}, e^{iαA} → the spectral integrals ∫e^{−αx}dQ(x), ∫e^{iαx}dQ(x) of the projection-valued measure Q with A = ∫x dQ(x); reason: the standard functional calculus; every self-adjoint A has such a Q; Reading 7
--   - encoding: A ≥ −c → −c‖x‖² ≤ Re⟪x, Ax⟫ for every x ∈ D(A); reason: the standard meaning of a lower bound of a self-adjoint operator
--   - encoding: there exists a unique self-adjoint operator A → A is unique among the operators satisfying IsLocalSemigroupGenerator (densely defined, self-adjoint, with a projection-valued measure Q and A = ∫x dQ(x)); reason: by the spectral theorem every self-adjoint operator has such a Q, so this is uniqueness among all self-adjoint operators
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, Theorem 6.2, p. 11; Definition 6.1, pp. 10–11

import Mathlib
import Definitions.Def_JRCurvedQFT_Symmetries_IsSymmetricLocalSemigroup
import Definitions.Def_JRCurvedQFT_Symmetries_IsLocalSemigroupGenerator
import Definitions.Def_JRCurvedQFT_Symmetries_pmapApply

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory

namespace JRCurvedQFT.Symmetries

/-- **Theorem 6.2 (Klein–Landau, Fröhlich).** A symmetric local semigroup has a unique self-adjoint
generator `A`: `𝒟_α ⊂ D(e^{−αA})` and `S_α = e^{−αA}|_{𝒟_α}` for all `α ∈ [0, T]`. Moreover, for every real
`c`, `A ≥ −c` if and only if `‖S_α f‖ ≤ e^{cα}‖f‖` for all `f ∈ 𝒟_α` and `0 < α < T`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, Theorem 6.2, p. 11, citing Klein–Landau (J. Funct. Anal. 44, 1981) and Fröhlich.

**Formalization Note** `A ≥ −c` is `−c‖x‖² ≤ Re⟪x, Ax⟫` on `D(A)`. Uniqueness is among all operators
that are `IsLocalSemigroupGenerator`, which by the spectral theorem are all the self-adjoint
operators with the property. -/
theorem theorem_6_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : ℝ} {D : ℝ → Submodule ℂ H} {S : ℝ → (H →ₗ.[ℂ] H)}
    (h : IsSymmetricLocalSemigroup T D S) :
    ∃ A : H →ₗ.[ℂ] H, IsLocalSemigroupGenerator T D S A ∧
      (∀ A' : H →ₗ.[ℂ] H, IsLocalSemigroupGenerator T D S A' → A' = A) ∧
      ∀ c : ℝ, (∀ x : A.domain, -c * ‖(x : H)‖ ^ 2 ≤ (⟪(x : H), A x⟫_ℂ).re) ↔
        ∀ α ∈ Set.Ioo 0 T, ∀ f ∈ D α, ‖pmapApply (S α) f‖ ≤ Real.exp (c * α) * ‖f‖ := by sorry

end JRCurvedQFT.Symmetries
