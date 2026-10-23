-- Prove2me | Theorems.Thm_OfflineCensoredPricing_Identifiability_theorem_2
-- name    : OfflineCensoredPricing.Identifiability.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:33.823828+00:00
-- url     : https://prove2.me/theorems/ba4bc870-0ac8-4edf-9fd8-dd55e0908192
-- title:
--   Theorem 2, p. 21 — if p*_max = p*_min and N ≥ C ε⁻² log(8K/δ), D2ACD has worst-case revenue loss ≤ ε with probability ≥ 1 − δ
-- statement:
--   Fix an instance satisfying the standing assumptions, with data size $N = \min_i N_i$ and the constant
--   $$C = \max\Big\{576(y+\bar b\bar p)^2\bar p^2,\ \frac{576\,C_1^2}{\frac1K\sum_{i}(p_i - \frac1K\sum_j p_j)^2\underline g^2},\ 288\,C_2^2,\ 288\,\bar p^2\bar\lambda^2\Big\}$$
--   (with $\bar\lambda$, $C_1$, $C_2$ as in Lemma 2). Suppose $p^*_{\max} = p^*_{\min}$. For any $\varepsilon > 0$ and $\delta \in (0,1)$, if $N \ge N(\varepsilon,\delta) = C\frac1{\varepsilon^2}\log\frac{8K}\delta$, then
--   $$\mathbb P\Big[\max_{F\in\mathcal F}\{R_F(p^*_F) - R_F(p^{\mathrm{D2ACD}})\} \le \varepsilon\Big] \ge 1 - \delta.$$
--
--   In identifiable problems D2ACD is near-optimal with sample complexity $O(\varepsilon^{-2}\log(1/\delta))$; this is the "if" half of Theorem 1.
--
--   **Formalization Note** The paper writes "for some constant $C$"; the statement uses the explicit $C$ of the proof (p. 32), which depends on the instance. It is made on the data assumption $\hat\gamma_i > 0$ for every $i$ (p. 10): the outer probability of $\{\text{loss} > \varepsilon\} \cap \{\hat\gamma_i > 0\ \forall i\}$ is at most $\delta$. $N(\varepsilon,\delta) > 0$, so every $N_i \ge 1$.
-- source:
--   Bu, Simchi-Levi & Wang, SSRN 3619625 (PDF of 2021-08-23), p. 21, Theorem 2; constant C from its proof, Appendix, p. 32

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Definitions.Def_OfflineCensoredPricing_Identifiability_D2ACD

namespace OfflineCensoredPricing.Identifiability

open MeasureTheory Set

/-- **Theorem 2** (Sample complexity for identifiable problems, p. 21, with the constant `C` of its
proof, p. 32). Suppose `p*_max = p*_min`. For any `ε > 0` and `δ ∈ (0, 1)`, if
`N ≥ N(ε, δ) = C ε⁻² log(8K/δ)` with
`C = max{576(y + b̄p̄)²p̄², 576C₁²/((1/K)∑ᵢ(pᵢ − (1/K)∑ⱼpⱼ)²g̲²), 288C₂², 288p̄²λ̄²}`, then with probability
at least `1 − δ` the worst-case revenue loss of D2ACD is at most `ε`. Stated on the data assumption
`γ̂ᵢ > 0` for all `i` (p. 10). -/
theorem theorem_2 {K : ℕ} [NeZero K] (I : Instance K) (hI : I.Standing)
    (heq : pStarMax I = pStarMin I) {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Nv : Fin K → ℕ) (hN : Cthm2 I * (1 / ε ^ 2) * Real.log (8 * K / δ) ≤ (Nmin Nv : ℝ)) :
    dataLaw I Nv {ω | ε < worstLoss I (d2acd I.toPublic Nv (sales I ω)) ∧
        ∀ i, 0 < gammaHat I.toPublic (sales I ω) i} ≤ ENNReal.ofReal δ := by sorry

end OfflineCensoredPricing.Identifiability
