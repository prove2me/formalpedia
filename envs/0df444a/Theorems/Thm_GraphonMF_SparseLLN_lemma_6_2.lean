-- Prove2me | Theorems.Thm_GraphonMF_SparseLLN_lemma_6_2
-- name    : GraphonMF.SparseLLN.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:56.347084+00:00
-- url     : https://prove2.me/theorems/83fd7c37-ec57-4a1c-aa6e-7bf9ed98d04d
-- title:
--   Lemma 6.2 applied to the state-only-diffusion limit
-- statement:
--   Let $X_u$ solve the limiting graphon equation (4.2), with Condition 4.1 and both parts of Condition 2.2. Its independent, generally nonidentically distributed paths have laws $\mu_u$. Their empirical law converges in probability, in the weak topology on probability measures over $\mathcal C_d$, to the averaged law:
--
--   $$\frac1n\sum_{i=1}^{n}\delta_{X_{i/n}}\ \xrightarrow{\mathbb P}\ \bar\mu:=\int_I\mu_u\,du.$$
--
--   This supplies the law of large numbers for the continuum particles used when proving convergence of the finite system.
--
--   **Formalization Note** Lemma 6.2 is printed for (2.1) under Condition 2.1. Section 7.2 applies it to the special system (4.2); the paper says Remark 5.2 permits Condition 4.1 in this bounded-coefficient case. This item states that application. Convergence in probability is expressed through outer probabilities of leaving neighborhoods of $\bar\mu$.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), pp. 3607, 3616, Lemma 6.2 and §7.2 (7.17); https://doi.org/10.1214/22-AAP1901

import Definitions.Def_GraphonMF_SparseLLN_Setting

open MeasureTheory Filter Topology
open scoped NNReal
set_option autoImplicit false

namespace GraphonMF.SparseLLN

/-- Lemma 6.2, p. 3607, applied to the state-only-diffusion system (4.2). -/
theorem lemma_6_2
    {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hT : 0 < T) (hd : 0 < d)
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d)
    (hnoise : NoiseSetting P X0 B)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G)
    (b : Vec d → Vec d → Vec d) (σ : Vec d → Matrix (Fin d) (Fin d) ℝ)
    (β : ℕ → ℝ) (h41 : Cond41 (initialLaw P X0) b σ β)
    (N : ℕ) (J : Fin N → Set GraphonMF.Stability.I)
    (h22a : Cond22a (initialLaw P X0) J) (h22b : Cond22b G J)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d)
    (hX : IsGraphonSolution42 P X0 B hnoise G b σ X) :
    ConvergesInProbability P (continuumEmpiricalSeq X) (solutionMixture hX) := by sorry

end GraphonMF.SparseLLN
