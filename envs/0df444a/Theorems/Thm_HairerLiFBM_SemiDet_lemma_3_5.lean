-- Prove2me | Theorems.Thm_HairerLiFBM_SemiDet_lemma_3_5
-- name    : HairerLiFBM.SemiDet.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:17.902695+00:00
-- url     : https://prove2.me/theorems/56da9d8e-edb3-4b36-a5e2-1fdb4ec2e690
-- title:
--   Lemma 3.5 — stochastic sewing lemma
-- statement:
--   Let $A_{s,t}$ be a continuous two-parameter $L^p$ process on a finite interval $[a,b]$, adapted at time $t$, with $p\ge2$. Suppose that its $L^p$ size is bounded by $K_1|t-s|^\eta$ for $\eta>1/2$, and the $L^p$ size of the conditional expectation of its defect $A_{s,t}-A_{s,u}-A_{u,t}$ is bounded by $K_2|t-s|^{\bar\eta}$ for $\bar\eta>1$. Then its Riemann sums converge in $L^p$ along every partition with mesh tending to zero, to an additive increment $I_{s,t}(A)$. Moreover,
--
--   $$\|I_{s,t}(A)\|_{L^p}\le C\left(K_2|t-s|^{\bar\eta}+K_1|t-s|^\eta\right),\qquad \|\mathbb E[I_{s,t}(A)-A_{s,t}\mid\mathcal F_s]\|_{L^p}\le C K_2|t-s|^{\bar\eta}.$$
--
--   If the conditional expectation of $A_{s,t}$ also has order $|t-s|^{\bar\eta}$, the sewn increment vanishes. The constant $C$ depends only on $p,\eta,\bar\eta$. This is the sewing result used to construct the integral in Lemma 3.10.
--
--   **Formalization Note** The constants $K_1,K_2$ are arbitrary upper bounds for the two seminorms defined in (3.8)–(3.9). Additivity and vanishing are equalities almost everywhere. The interval is taken with $a<b$, as in the paper's partition setting.
-- source:
--   Hairer and Li, Averaging dynamics driven by fractional Brownian motion, Ann. Probab. 48(4) (2020), https://doi.org/10.1214/19-AOP1408, p. 1834, Lemma 3.5, (3.8)–(3.10); quoted there from Lê, Theorem 2.1, https://arxiv.org/abs/1810.10500

import Mathlib
import Definitions.Def_HairerLiFBM_SemiDet_Model

namespace HairerLiFBM.SemiDet

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Lemma 3.5, p. 1834: the stochastic sewing lemma quoted from Lê. -/
theorem lemma_3_5 :
    ∀ (p η ηbar : ℝ), 2 ≤ p → 1 / 2 < η → 1 < ηbar →
      ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ) (a b : ℝ) (hn : 0 < n) (hab : a < b)
          {Ω : Type*} [mΩ : MeasurableSpace Ω]
          (P : Measure Ω) [IsProbabilityMeasure P]
          (ℱ : Filtration ℝ mΩ)
          (A : ℝ → ℝ → Ω → E n) (K1 K2 : ℝ),
          (∀ s t, a ≤ s → s ≤ t → t ≤ b →
            StronglyMeasurable[ℱ t] (A s t) ∧
              MemLp (A s t) (ENNReal.ofReal p) P) →
          (∀ s t, a ≤ s → s ≤ t → t ≤ b →
            Tendsto (fun q : ℝ × ℝ =>
              eLpNorm (fun ω => A q.1 q.2 ω - A s t ω) (ENNReal.ofReal p) P)
              (𝓝[{q : ℝ × ℝ | a ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ b}] (s, t))
              (𝓝 (0 : ℝ≥0∞))) →
          (∀ s t, a ≤ s → s < t → t ≤ b →
            eLpNorm (A s t) (ENNReal.ofReal p) P ≤
              ENNReal.ofReal (K1 * (t - s) ^ η)) →
          (∀ s u t, a ≤ s → s < u → u < t → t ≤ b →
            eLpNorm (P[fun ω => A s t ω - A s u ω - A u t ω | ℱ s])
              (ENNReal.ofReal p) P ≤
              ENNReal.ofReal (K2 * (t - s) ^ ηbar)) →
          ∃ I : ℝ → ℝ → Ω → E n,
            (∀ s t, a ≤ s → s ≤ t → t ≤ b →
              ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
                ∀ π : Partition s t, π.mesh < δ →
                  eLpNorm (fun ω =>
                    (∑ i : Fin π.n, A (π.pt i.castSucc) (π.pt i.succ) ω) - I s t ω)
                    (ENNReal.ofReal p) P < ENNReal.ofReal ε) ∧
            (∀ s t, a ≤ s → s ≤ t → t ≤ b →
              eLpNorm (I s t) (ENNReal.ofReal p) P ≤
                ENNReal.ofReal (C * (K2 * (t - s) ^ ηbar + K1 * (t - s) ^ η))) ∧
            (∀ s t, a ≤ s → s ≤ t → t ≤ b →
              eLpNorm (P[fun ω => I s t ω - A s t ω | ℱ s])
                (ENNReal.ofReal p) P ≤
                ENNReal.ofReal (C * K2 * (t - s) ^ ηbar)) ∧
            (∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
              (fun ω => I s u ω + I u t ω) =ᵐ[P] I s t) ∧
            ((∃ K3 : ℝ, ∀ s t, a ≤ s → s < t → t ≤ b →
                eLpNorm (P[A s t | ℱ s]) (ENNReal.ofReal p) P ≤
                  ENNReal.ofReal (K3 * (t - s) ^ ηbar)) →
              ∀ s t, a ≤ s → s ≤ t → t ≤ b →
                I s t =ᵐ[P] (fun _ => (0 : E n))) := by sorry

end HairerLiFBM.SemiDet
