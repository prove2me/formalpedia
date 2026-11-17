-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_theorem_A_3
-- name    : GrothendieckLB.Supplement.theorem_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:45:03.452283+00:00
-- url     : https://prove2.me/theorems/11b3ea9c-93eb-4822-9f3c-f73e0fd142cb
-- title:
--   Theorem A.3: mixed Krivine preprocessing, $K_G\le\pi/(2\gamma)$
-- statement:
--   Let $L\in\mathbb N$ and, for each $\ell\in\{1,\dots,L\}$, let $f_\ell,g_\ell:\mathbb R^{k_\ell}\to\{-1,1\}$ be odd measurable functions with arcsine-normalized correlation function
--   $$
--   H_\ell(t)=\frac\pi2\,\mathbb E\Bigl[f_\ell(G_1)\,g_\ell\bigl(tG_1+\sqrt{1-t^2}\,G_2\bigr)\Bigr].
--   $$
--   Let $\lambda_1,\dots,\lambda_L\ge0$ with $\sum_\ell\lambda_\ell=1$, and set $H_\lambda(t)=\sum_{\ell=1}^L\lambda_\ell H_\ell(t)$. Suppose that $H_\lambda$ has a local inverse at the origin, $H_\lambda^{-1}(\zeta)=\sum_{r\ge1}a_r\zeta^r$, holomorphic on a neighborhood of $\gamma\overline{\mathbb D}$, and that
--   $$
--   M_\lambda(\gamma):=\sum_{r\ge1}|a_r|\,\gamma^r\le1 .
--   $$
--   Then
--   $$
--   K_G\le\frac{\pi}{2\gamma}.
--   $$
--
--   Mixing finitely many schemes, possibly of different dimensions, is thus as good as a single scheme for the inverse-majorant bound.
--
--   **Formalization Note** The index set is $\{0,\dots,L-1\}$; each $(f_\ell,g_\ell)$ is a published `KrivineScheme (k ℓ)` with its `correlationFunction`. Holomorphy and $\gamma>0$ are encoded as in Theorem A.1.
--
--   Differences from the source:
--   - encoding: γ D with γ > 0 implicit (a disk of radius γ) → explicit hypothesis 0 < γ; reason: as in Theorem A.1: the condition only excludes the undefined case γ = 0
--   - encoding: H_λ⁻¹ holomorphic on a neighborhood of γD → ∑ |a_r| R^r converges for some R > γ; reason: as in Theorem A.1; same instances
--   - encoding: ℓ ∈ {1, …, L} → ℓ : Fin L (0-based); reason: index shift only
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem A.3, p.49

import Mathlib
import Definitions.Def_GrothendieckConstantDefs
import Definitions.Def_KrivineSchemeDefs
import Definitions.Def_GrothendieckLB_IsLocalInverseBranch
import Definitions.Def_GrothendieckLB_taylorCoeff

namespace GrothendieckLB

namespace Supplement

/-- Theorem A.3, mixed Krivine preprocessing and projection (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem A.3, p.49): let `L ∈ ℕ`
and, for `ℓ ∈ {1, …, L}`, let `f_ℓ, g_ℓ : ℝ^{k_ℓ} → {−1, 1}` be odd measurable functions with
arcsine-normalized correlation function `H_ℓ`. Let `λ₁, …, λ_L ≥ 0` with `∑ λ_ℓ = 1` and
`H_λ(t) := ∑_ℓ λ_ℓ H_ℓ(t)`. Suppose `H_λ` has a local inverse at the origin,
`H_λ⁻¹(ζ) = ∑_{r ≥ 1} a_r ζ^r`, holomorphic on a neighborhood of `γD`, and
`M_λ(γ) := ∑_{r ≥ 1} |a_r| γ^r ≤ 1`. Then `K_G ≤ π/(2γ)`.

**Formalization Note** The index set is `Fin L` (0-based); the dimensions `k ℓ` may differ.
Each `(f_ℓ, g_ℓ)` is a published `GrothendieckConstant.KrivineScheme (k ℓ)` and `H_ℓ` its
`correlationFunction` (see Theorem A.1). The weights are `lam`. Holomorphy on a neighborhood of
`γD` and `γ > 0` are encoded as in Theorem A.1. -/
theorem theorem_A_3 (L : ℕ) (k : Fin L → ℕ)
    (S : (ℓ : Fin L) → GrothendieckConstant.KrivineScheme (k ℓ)) (lam : Fin L → ℝ)
    (hlam_nonneg : ∀ ℓ, 0 ≤ lam ℓ) (hlam_sum : ∑ ℓ, lam ℓ = 1) (G : ℝ → ℝ)
    (hG : IsLocalInverseBranch
      (fun t => ∑ ℓ, lam ℓ * GrothendieckConstant.correlationFunction (S ℓ) t) G)
    (γ : ℝ) (hγ : 0 < γ)
    (hhol : ∃ R : ℝ, γ < R ∧ Summable (fun r => |taylorCoeff r G| * R ^ r))
    (hM : ∑' r : ℕ, |taylorCoeff (r + 1) G| * γ ^ (r + 1) ≤ 1) :
    GrothendieckConstant.grothendieckConst ≤ Real.pi / (2 * γ) := by sorry

end Supplement

end GrothendieckLB
