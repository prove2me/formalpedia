-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_eq_4_69
-- name    : LeakageRefresh.Continual.eq_4_69
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:11:49.612979+00:00
-- url     : https://prove2.me/theorems/468b734c-2e47-4dc9-9024-6e6087ce1076
-- title:
--   §4.7, Eq. (4.69) — the moving-boundary hybrid: $\delta(P_0^T,P_1^T)\le C\,T\,K^3(\varepsilon+\mathrm{disc}_n/\beta)$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $n\ge2$, $T\ge1$, $\lambda\ge0$, $q=2^n-1$, $K=2^{2\lambda}$, $\beta=q^{-1/3}$ and $\mathrm{disc}_n=3/\sqrt{q-1}$. Fix a deterministic strategy and $\varepsilon$, and for every round $i$, formal incoming history $h$ and answer $z$ let $G_{i,h,z}$ be a table satisfying the conclusions (4.58)–(4.64) of Lemma 4.13 with these $\beta$ and $\varepsilon$. Then
--   $$\delta\big(P_0^T,P_1^T\big)\le C\cdot T\cdot K^3\cdot\Big(\varepsilon+\frac{\mathrm{disc}_n}{\beta}\Big). \tag{4.69}$$
--   This is the hybrid argument that moves the boundary between states labelled $1$ and $0$ along the chain, one state at a time.
--
--   Differences from the source:
--   - generalization: the tables $G_{i,h,z}$ of Lemma 4.13, with $\varepsilon=Cq^{-1/9}$ → every family of tables satisfying (4.58)–(4.64) with $\beta=q^{-1/3}$ and an arbitrary $\varepsilon$; reason: the argument uses only these conclusions; Lemma 4.13's family is one such family, so the statement specializes to the paper's (4.69)
--   - encoding: rounds $i\in\{1,\dots,T\}$ with incoming history $h\in\mathcal Z^{i-1}$ → `i : Fin T` is round $i+1$, with incoming history `Fin i → Answer lam`; reason: 0-based indexing of the same rounds and histories
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 45, §4.7, Eq. (4.69)

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding
import Definitions.Def_LeakageRefresh_Continual_LeakageModel
import Definitions.Def_LeakageRefresh_Continual_Tables
import Definitions.Def_LeakageRefresh_Continual_OneRound

namespace LeakageRefresh.Continual

/-- **§4.7, Eq. (4.69) (moving-boundary hybrid).** There is an absolute constant `C > 0` such that
for every `n ≥ 2`, `T ≥ 1`, `λ` (here `lam`), every deterministic strategy `σ`, every `ε` and
every family of tables `G i h z` satisfying the conclusions (4.58)–(4.64) of Lemma 4.13 with
`β = q^{−1/3}` and this `ε` (`q = 2ⁿ − 1`, `K = 2^{2λ}`):
`δ(P₀ᵀ, P₁ᵀ) ≤ C · T · K³ · (ε + disc_n/β)`. -/
theorem eq_4_69 :
    ∃ C : ℝ, 0 < C ∧
      ∀ n T lam : ℕ, 2 ≤ n → 1 ≤ T →
      ∀ (σ : Strategy n T lam) (ε : ℝ)
        (G : (i : Fin T) → (Fin i → Answer lam) → Answer lam → Table4 n),
        (∀ i h z, IsLocalApprox (σ i h) z (((2 : ℝ) ^ n - 1) ^ (-(1 / 3 : ℝ))) ε (G i h z)) →
        statDist (transcriptLaw σ 0) (transcriptLaw σ 1) ≤
          C * (T : ℝ) * ((2 : ℝ) ^ (2 * lam)) ^ 3 *
            (ε + disc n / ((2 : ℝ) ^ n - 1) ^ (-(1 / 3 : ℝ))) := by sorry

end LeakageRefresh.Continual
