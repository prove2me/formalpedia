-- Prove2me | Theorems.Thm_GraphonMF_DenseLLN_lemma_6_2
-- name    : GraphonMF.DenseLLN.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:35.304399+00:00
-- url     : https://prove2.me/theorems/09a5e24e-9eca-44c9-8a57-b5c78b437a4b
-- title:
--   Lemma 6.2, p. 3607 — (1/n) Σᵢ δ_{X_{i/n}} → μ̄ in 𝒫(𝒞_d) in probability
-- statement:
--   Assume Conditions 2.1 and 2.2, let $G$ be a graphon and let $X=(X_u)_{u\in I}$ solve the graphon particle system (2.1), with path laws $\mu_u$ and averaged law $\bar\mu=\int_I\mu_u\,du$. Let
--   $$\bar\mu^n:=\frac1n\sum_{i=1}^n\delta_{X_{i/n}} .$$
--   Then $\bar\mu^n\to\bar\mu$ in $\mathcal P(\mathcal C_d)$ in probability as $n\to\infty$: for every weak-topology neighbourhood $U$ of $\bar\mu$,
--   $$\mathbb P\big(\bar\mu^n\notin U\big)\longrightarrow0 .$$
--
--   This is a law of large numbers for the independent but not identically distributed continuum particles $X_{1/n},\dots,X_{n/n}$. In the proof of Theorem 3.1 it is applied to the solution for a continuous graphon $\tilde G$ (display (6.13)).
--
--   **Formalization Note** Convergence in probability is taken in the space of probability measures on $\mathcal C_d$ with the topology of weak convergence, and $\mathbb P$ is applied as an outer measure, so no measurability of the event is required. The independence of $X_{i/n}$ across $i$ is not an extra hypothesis: each $X_u$ is adapted to the natural filtration of $(X_u(0),B_u)$, and these are independent across $u$ by the noise setting.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3607, Lemma 6.2

import Mathlib
import Definitions.Def_GraphonMF_DenseLLN_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.DenseLLN
theorem lemma_6_2 {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d N : ℕ} {P : Measure Ω}
    {μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)} {X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d}
    (noise : NoiseSetting P μ0 X0 B) (hT : 0 < T)
    (b : GraphonMF.Stability.State d → GraphonMF.Stability.State d → GraphonMF.Stability.State d) (σ : GraphonMF.Stability.State d → GraphonMF.Stability.State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (h21 : GraphonMF.Stability.Cond21 ε μ0 b σ)
    (J : Fin N → Set GraphonMF.Stability.I) (h22a : Cond22a μ0 J)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G) (h22b : Cond22b G J)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) (hX : IsGraphonSolution noise G b σ X) :
    TendstoInProb P (fun n ω => empiricalPM (fun i => X (GraphonMF.Stability.lab n i) ω)) (mixturePM P X) := by sorry
end GraphonMF.DenseLLN
