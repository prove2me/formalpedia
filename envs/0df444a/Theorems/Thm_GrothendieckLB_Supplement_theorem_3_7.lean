-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_theorem_3_7
-- name    : GrothendieckLB.Supplement.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:42:00.530836+00:00
-- url     : https://prove2.me/theorems/d551befb-b758-41e7-9c50-c57fe59ef7ec
-- title:
--   Theorem 3.7: finite-dimensional approximation of limiting schemes
-- statement:
--   Let $S=(f,g,\rho_1,\dots,\rho_k)$ be a limiting Krivine scheme with correlation function $H_S$. Then
--
--   1. $H_S$ extends holomorphically to the complex unit disk $\mathbb D=\{z\in\mathbb C:|z|<1\}$, and
--   2. there is a sequence of ordinary finite-dimensional Krivine schemes $S_1,S_2,\dots$ of increasing dimension whose correlation functions satisfy
--   $$
--   H_{S_N}\longrightarrow H_S\quad\text{uniformly on every compact subset of }\mathbb D .
--   $$
--
--   This is what lets an inverse-majorant certificate for a low-dimensional limiting scheme be transferred to genuine high-dimensional rounding schemes.
--
--   **Formalization Note** The extension of $H_S$ is a function $F:\mathbb C\to\mathbb C$ complex differentiable on $\mathbb D$ and equal to $H_S$ on $(-1,1)$ (unique by the identity theorem). The ordinary schemes are the published `KrivineScheme (d N)` with the published `correlationFunction`, and the convergence is locally uniform convergence on $\mathbb D$ of their holomorphic extensions.
--
--   Differences from the source:
--   - reading: a sequence of ordinary schemes of increasing dimension → dimensions d N strictly increasing (StrictMono d); reason: the stronger of the two readings (strict vs non-decreasing); any sequence with d N → ∞ has a strictly increasing subsequence along which the convergence persists
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 3.7, p.18

import Mathlib
import Definitions.Def_KrivineSchemeDefs
import Definitions.Def_GrothendieckLB_Supplement_LimitingScheme_corr
open Filter

namespace GrothendieckLB

namespace Supplement

/-- Theorem 3.7, finite-dimensional approximation of limiting schemes (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 3.7, p.18):
let `S = (f, g, ρ₁, …, ρ_k)` be a limiting Krivine scheme. Then its correlation function `H_S`
extends holomorphically to the complex unit disk `D`. Moreover, there exists a sequence of
ordinary finite-dimensional Krivine schemes `S₁, S₂, …` of increasing dimension, whose correlation
functions satisfy `H_{S_N} → H_S` uniformly on every compact subset of `D`.

**Formalization Note** The holomorphic extension of `H_S` is a function `F : ℂ → ℂ` complex
differentiable on `D = Metric.ball 0 1` and equal to `H_S` on `(−1, 1)`; it is unique by the
identity theorem, so the existential is faithful. The ordinary schemes are the published
`GrothendieckConstant.KrivineScheme (d N)` with correlation function
`GrothendieckConstant.correlationFunction`; "`H_{S_N} → H_S` on compact subsets of `D`" is
`TendstoLocallyUniformlyOn` (equivalent on the open set `D`) of their holomorphic extensions
`F_N` to `F`. "Increasing dimension" is read as strictly increasing `d`. -/
theorem theorem_3_7 {k : ℕ} (S : LimitingScheme k) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 1) ∧
      (∀ t : ℝ, |t| < 1 → F t = (S.corr t : ℂ)) ∧
      ∃ (d : ℕ → ℕ) (T : (N : ℕ) → GrothendieckConstant.KrivineScheme (d N))
        (FN : ℕ → ℂ → ℂ), StrictMono d ∧
        (∀ N, DifferentiableOn ℂ (FN N) (Metric.ball 0 1) ∧
          ∀ t : ℝ, |t| < 1 →
            FN N t = (GrothendieckConstant.correlationFunction (T N) t : ℂ)) ∧
        TendstoLocallyUniformlyOn FN F atTop (Metric.ball 0 1) := by sorry

end Supplement

end GrothendieckLB
