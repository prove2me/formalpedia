-- Prove2me | Theorems.Thm_HeilmanMax3Cut_Supplement_theorem_2_1
-- name    : HeilmanMax3Cut.Supplement.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:09:36.333739+00:00
-- url     : https://prove2.me/theorems/23e34ee4-e5d0-4915-864a-eb3b0df6085e
-- title:
--   Theorem 2.1 — negative vector-valued Borell inequality $\mathrm{Stab}_\rho(f)\ge F^*(k,\rho)$
-- statement:
--   Let $n\ge k\ge3$, let $f:\mathbb R^n\to B_k$ be measurable, where $B_k$ is the closed unit ball of $\mathbb R^k$, and let $-0.5843\le\rho<0$ (or $-3/5\le\rho<0$ if $k>3$). Then
--
--   $$\mathrm{Stab}_\rho(f)\ \ge\ F^*(k,\rho).$$
--
--   Since $F^*(k,\rho)$ is the noise stability of $f_{\mathrm{opt},k}(x)=(x_1,\dots,x_k)/\|(x_1,\dots,x_k)\|$, the function $f_{\mathrm{opt},k}$ minimizes noise stability at these negative correlations; with $k=3$ and [HNP+23, Theorem 11.3] this yields Theorem 1.7.
--
--   **Formalization Note** $0.5843$ is the exact decimal $5843/10000$. The range is the disjunction of the two printed ranges.
--
--   Differences from the source: none.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Theorem 2.1, p.9, Eq. (4)

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HeilmanMax3Cut_Supplement_stabVec
import Definitions.Def_HeilmanMax3Cut_Supplement_Fstar
open OAI.GaussianPropeller

namespace HeilmanMax3Cut.Supplement

/-- **Theorem 2.1 (Negative vector-valued Borell inequality).** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Theorem 2.1, p.9: "Let
`n ≥ k ≥ 3`, let `f : ℝⁿ → B_k` be measurable, and let `−0.5843 ≤ ρ < 0` (or `−3/5 ≤ ρ < 0` if
`k > 3`). Then `Stab_ρ(f) ≥ F*(k, ρ)`. (4)"

**Formalization Note.** `f : Space n → EuclideanSpace ℝ (Fin k)` is measurable with `‖f x‖ ≤ 1` for
every `x` (values in `B_k`). The correlation range is `ρ < 0` together with `−0.5843 ≤ ρ`, or, when
`k > 3`, `−3/5 ≤ ρ`; `0.5843` is the exact decimal `5843/10000`. `Stab_ρ` is `stabVec` and `F*` is
the closed form (3), `Fstar`. -/
theorem theorem_2_1 (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n)
    (f : Space n → EuclideanSpace ℝ (Fin k)) (hf : Measurable f) (hB : ∀ x, ‖f x‖ ≤ 1)
    (ρ : ℝ) (hρ : ρ < 0) (hρ' : -(5843 / 10000 : ℝ) ≤ ρ ∨ (3 < k ∧ -(3 / 5 : ℝ) ≤ ρ)) :
    Fstar k ρ ≤ stabVec n k ρ f := by sorry

end HeilmanMax3Cut.Supplement
