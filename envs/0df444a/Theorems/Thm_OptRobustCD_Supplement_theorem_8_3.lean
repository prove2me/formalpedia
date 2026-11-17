-- Prove2me | Theorems.Thm_OptRobustCD_Supplement_theorem_8_3
-- name    : OptRobustCD.Supplement.theorem_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:52:04.431548+00:00
-- url     : https://prove2.me/theorems/211ad8db-ca3d-4631-8882-c971833a8360
-- title:
--   Theorem 8.3 — nearby-point entropy descent: $F(\bar X)-\min_{\mathcal S}F\le\frac{\log n}{\eta T}+2\eta\max_t\|H_t\|_{op}^2+\frac1T\sum_t\langle H_t,\widetilde X_t-X_t\rangle$
-- statement:
--   Let $n\ge2$ and let $\mathcal S=\{X\in\mathbb R^{n\times n}: X\succeq0,\ \operatorname{Tr}X=1\}$ be the density matrices, with $\langle B,C\rangle=\operatorname{Tr}(B^{\mathsf T}C)$. Let $F$ be a real-valued function, convex on the real symmetric $n\times n$ matrices, that attains its minimum over $\mathcal S$. Let $\eta>0$, let $T\ge1$ be an integer, and let $H_1,\dots,H_T$ be real symmetric $n\times n$ matrices. For $1\le t\le T$ define the matrix multiplicative weights iterates
--   $$
--   S_t=-\eta\sum_{s<t}H_s,\qquad X_t=\frac{e^{S_t}}{\operatorname{Tr}e^{S_t}}.
--   $$
--   Suppose $\widetilde X_1,\dots,\widetilde X_T\in\mathcal S$ satisfy $H_t\in\partial F(\widetilde X_t)$ for $1\le t\le T$, where $\partial F$ is the subdifferential over the symmetric matrices. Then the average $\bar X=T^{-1}\sum_{t=1}^T\widetilde X_t$ satisfies
--   $$
--   F(\bar X)-\min_{\mathcal S}F\ \le\ \frac{\log n}{\eta T}+2\eta\max_{1\le t\le T}\|H_t\|_{op}^2+\frac1T\sum_{t=1}^T\langle H_t,\widetilde X_t-X_t\rangle ,
--   $$
--   where $\|\cdot\|_{op}$ is the spectral norm and $\log$ the natural logarithm.
--
--   The subgradients are computed at points $\widetilde X_t$ that only approximate the exact iterates $X_t$ (for instance through a low-rank sketch of $e^{S_t}$); the last term charges for that approximation, and may be negative. This is the convergence guarantee behind the nearly-linear-time solver of Theorem 8.2.
--
--   **Formalization Note** "Attains its minimum over $\mathcal S$" is the existence of a minimizer in $\mathcal S$, and $\min_{\mathcal S}F$ is written as the infimum of $F$ over $\mathcal S$, which then equals that minimum. The maximum is a finite maximum over $\{1,\dots,T\}$; the spectral norm is the operator norm on Euclidean space.
--
--   Differences from the source:
--   - encoding: F convex on all real symmetric matrices → F : ℝ^{n×n} → ℝ with ConvexOn ℝ {X | X.IsSymm} F; reason: values of F off the symmetric matrices never enter the statement or ∂F
--   - encoding: F attains its minimum over S, and min_S F → ∃ U ∈ S with F U ≤ F V for all V ∈ S, and sInf (F '' S); reason: the infimum equals the attained minimum, so the instances are the same
--   - encoding: H_1, …, H_T and X̃_1, …, X̃_T → sequences indexed by ℕ whose entries 1, …, T are constrained and used; reason: the other entries never enter (S_t sums over 1 ≤ s < t ≤ T)
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Theorem 8.3, p.40 (pdf p.42); restated with proof in Appendix B, pp.57–58 (pdf pp.59–60); standing assumption n ⩾ 2 and S from §8, p.37 (pdf p.39)

import Mathlib
import Definitions.Def_OptRobustCD_SDPObjective
import Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm
import Definitions.Def_OptRobustCD_Supplement_symSubdiff
import Definitions.Def_OptRobustCD_Supplement_mmwIterate

namespace OptRobustCD

namespace Supplement

open Finset

/-- **Theorem 8.3** (Nearby-point entropy descent). Hopkins, Hua, Mohanty, Rajaraman, Steurer,
*Optimal Robust Community Detection*, STOC 2027 submission (manuscript of November 3, 2026,
sha256 3d287d54…), Theorem 8.3, p.40 (pdf p.42); restated with proof in App. B, pp.57–58
(pdf pp.59–60).

"Let `F` be convex on all real symmetric matrices and attain its minimum over `S`. Let `η > 0`, let
`T ⩾ 1` be an integer, and let `H_1, …, H_T ∈ R^{n×n}` be symmetric matrices. For `1 ⩽ t ⩽ T`,
define `S_t = −η ∑_{s<t} H_s`, `X_t = e^{S_t} / Tr e^{S_t}`. Suppose `X̃_1, …, X̃_T ∈ S` satisfy
`H_t ∈ ∂F(X̃_t)` for `1 ⩽ t ⩽ T`. Then `X̄ = T^{−1} ∑_{t=1}^T X̃_t` satisfies
`F(X̄) − min_S F ⩽ log n/(ηT) + 2η max_{1⩽t⩽T} ∥H_t∥²_op + (1/T) ∑_{t=1}^T ⟨H_t, X̃_t − X_t⟩`."

**Formalization Note.**
* Standing assumption of §8 (p.37): `n ⩾ 2`. `S` is the published `densitySet n`
  (`X ⪰ 0`, `Tr X = 1`); `⟨B, C⟩ = Tr(BᵀC)`.
* "Convex on all real symmetric matrices" is `ConvexOn ℝ {X | X.IsSymm} F`; `F` is real-valued.
  "Attains its minimum over `S`" is the existence of a minimizer `U ∈ S`; `min_S F` is then
  `sInf (F '' S)`, which equals `F U`.
* The sequences `H`, `X̃` are indexed by `ℕ` with the paper's indices `1, …, T`; only those
  entries enter. `X_t` is `mmwIterate η H t` (`S_1 = 0`).
* `∥·∥_op` is the spectral norm (`HighDimProb.QuadraticForms.opNorm`, the operator norm on
  Euclidean space), and the maximum is `Finset.sup'` over `{1, …, T}`. `log` is the natural
  logarithm. -/
theorem theorem_8_3 {n : ℕ} (hn : 2 ≤ n) (F : Matrix (Fin n) (Fin n) ℝ → ℝ)
    (hF : ConvexOn ℝ {X : Matrix (Fin n) (Fin n) ℝ | X.IsSymm} F)
    (hmin : ∃ U ∈ densitySet n, ∀ V ∈ densitySet n, F U ≤ F V)
    (η : ℝ) (hη : 0 < η) (T : ℕ) (hT : 1 ≤ T)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (hH : ∀ t ∈ Icc 1 T, (H t).IsSymm)
    (Xtil : ℕ → Matrix (Fin n) (Fin n) ℝ) (hXtil : ∀ t ∈ Icc 1 T, Xtil t ∈ densitySet n)
    (hsub : ∀ t ∈ Icc 1 T, H t ∈ symSubdiff F (Xtil t)) :
    F ((T : ℝ)⁻¹ • ∑ t ∈ Icc 1 T, Xtil t) - sInf (F '' densitySet n) ≤
      Real.log n / (η * T)
        + 2 * η * (Icc 1 T).sup' (nonempty_Icc.mpr hT)
            (fun t => HighDimProb.QuadraticForms.opNorm (H t) ^ 2)
        + (1 / (T : ℝ)) * ∑ t ∈ Icc 1 T, ((H t).transpose * (Xtil t - mmwIterate η H t)).trace := by sorry

end Supplement

end OptRobustCD
