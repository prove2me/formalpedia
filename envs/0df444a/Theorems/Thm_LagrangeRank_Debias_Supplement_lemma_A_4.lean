-- Prove2me | Theorems.Thm_LagrangeRank_Debias_Supplement_lemma_A_4
-- name    : LagrangeRank.Debias.Supplement.lemma_A_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T03:50:18.325643+00:00
-- url     : https://prove2.me/theorems/9b5c3dc7-09a5-4250-b4ff-9a80a2801b1c
-- title:
--   Lemma A.4 (corrected: inverse action and conditional working event) — both score CLTs
-- statement:
--   Fix a bounded dynamic range $\kappa$, a positive regularization coefficient $c$, and a working-event constant $K>0$. For a sufficiently large constant $C_0$, let $n,L\to\infty$, $p\ge C_0\log n/n$ eventually, and
--   $$\frac{n\log n}{\sqrt L}+\frac{\log n}{\sqrt{pL}}\longrightarrow0.$$
--   Let the centered true scores have dynamic range at most $\kappa$. Condition on a sequence of comparison graphs. Require the conditional probability of failure of the (A.8)–(A.12) working event, including Lemma 3.1's estimation event, to tend to zero. The corrected (A.11) includes invertibility and the zero-sum $(v,0)$ action bound $K/(np)$, and therefore forces these graph properties eventually. For any distinct coordinate sequences $i,j$, both conditional limits hold:
--   $$\frac{\sqrt L\,[\Theta^*_{11}]_j\nabla\mathcal L(\theta^*)}{\sqrt{[\Theta^*_{11}]_{jj}}}\Rightarrow N(0,1),\qquad
--   \frac{\sqrt L\,([\Theta^*_{11}]_i-[\Theta^*_{11}]_j)\nabla\mathcal L(\theta^*)}{\sqrt{(e_i-e_j)^T\Theta^*_{11}(e_i-e_j)}}\Rightarrow N(0,1).$$
--   The law in each limit is the product Bernoulli outcome law with that graph fixed, retaining the actual graph-specific inverse. These are the two score CLTs supporting BTL normality.
--
--   Differences from the source:
--   - correction: the full-bordered-inverse equality (A.11) in the conditional hypotheses → invertibility and the inverse action bound on zero-sum (v,0); reason: the ±√n eigenvalues on p. 70 disprove the printed equality; (C.3) and both studentizers use the upper-left block, not the extra eigenspaces; disconnected graphs have no source inverse
--   - reading: conditioning on the graph and assuming (A.8)–(A.12) → a fixed graph sequence and a conditional working-event failure probability tending to zero, with the Lemma 3.1 event used on p. 47; reason: (A.8)–(A.10) also involve random outcomes, so they are not deterministic graph predicates; this explicitly resolves the conditioning language
--   - encoding: sample size n and repeated-comparison count L tend to infinity → a separate sequence index t, dimensions n(t), L(t), and finite product probability spaces; reason: the law at each problem size is exactly (2.1); both graph and comparison randomness remain
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 42, Lemma A.4

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Supplement_BTL

namespace LagrangeRank.Debias.Supplement

open MeasureTheory ProbabilityTheory Matrix Filter Topology
/-- Both conditional score CLTs, with the source's working-event interpretation made explicit. -/
theorem lemma_A_4 (κ c K : ℝ) (hκ : 1 ≤ κ) (hc : 0 < c) (hK : 0 < K) :
    ∃ C0 : ℝ, 0 < C0 ∧
    ∀ (n L : ℕ → ℕ) (p : ℕ → unitInterval) (θ : (t : ℕ) → Vec (n t))
      (g : (t : ℕ) → Graph (n t)) (i j : (t : ℕ) → Fin (n t)),
      Regime n L p → Density C0 n p → Rates32 n L p →
      (∀ t, Parameter κ (θ t)) → (∀ t, i t ≠ j t) →
      Tendsto (fun t => (outcomeLaw (L t) (θ t)
        {y | ¬SourceBounds (p t) c K (g t,y) (θ t)}).toReal) atTop (𝓝 0) →
      TendstoInDistribution (fun t y =>
        Real.sqrt (L t) * ((trueBlock (g t,y) (θ t)) *ᵥ grad (loss (g t,y)) (θ t)) (j t) /
          Real.sqrt (trueBlock (g t,y) (θ t) (j t) (j t)))
        atTop id (fun t => outcomeLaw (L t) (θ t)) (gaussianReal 0 1) ∧
      TendstoInDistribution (fun t y =>
        Real.sqrt (L t) *
          (((trueBlock (g t,y) (θ t)) *ᵥ grad (loss (g t,y)) (θ t)) (i t) -
           ((trueBlock (g t,y) (θ t)) *ᵥ grad (loss (g t,y)) (θ t)) (j t)) /
          Real.sqrt (pairVar (trueBlock (g t,y) (θ t)) (i t) (j t)))
        atTop id (fun t => outcomeLaw (L t) (θ t)) (gaussianReal 0 1) := by sorry

end LagrangeRank.Debias.Supplement
