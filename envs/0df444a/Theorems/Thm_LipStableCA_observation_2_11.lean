-- Prove2me | Theorems.Thm_LipStableCA_observation_2_11
-- name    : LipStableCA.observation_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:50:00.956733+00:00
-- url     : https://prove2.me/theorems/91fd7bf8-e93b-494a-b688-6969f26b2cbe
-- title:
--   Observation 2.11 — mixtures of TIE (ex-post IR) mechanisms are TIE (ex-post IR)
-- statement:
--   Let $\mu$ be a probability distribution on a set $\Xi$ and let $\{(S^\xi,p^\xi)\}_{\xi\in\Xi}$ be a family of randomized mechanisms. Let $(S,p)$ be the mechanism that draws $\xi\sim\mu$ independently of the report $v$ and then outputs $S^\xi(v)$ and $p^\xi(v)$.
--
--   1. If $(S^\xi,p^\xi)$ is truthful in expectation for almost every $\xi$, then $(S,p)$ is truthful in expectation.
--   2. If $(S^\xi,p^\xi)$ is ex-post individually rational for almost every $\xi$, then so is $(S,p)$.
--
--   It reduces Lemmas 4.3 and 4.4 to a fixed vector of discounts.
--
--   **Formalization Note.** The internal coins of the family live on one type, with a law that may depend on $\xi$.
--
--   Differences from the source:
--   - encoding: a family of mechanisms with internal coins → coins on one type $\Omega$ under a Markov kernel $\kappa$; reason: every family of coin laws on a common space is a kernel; a constant kernel covers Mechanism 2
--   - encoding: the expectations and probabilities of the mixture → joint measurability of allocation and payments, and joint integrability of payments, as hypotheses; reason: they are what makes the identities $\mathbb E=\int\mathbb E_\xi$ of the printed proof meaningful
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Observation 2.11, p.9

import Definitions.Def_LipStableCA_Mechanism
open MeasureTheory
open ProbabilityTheory

namespace LipStableCA

/-- **Observation 2.11.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.9. **Formalization Note.** coins on one type `Ω` under a Markov kernel `κ`: every family of coin laws on a common space is a kernel; a constant kernel covers Mechanism 2. joint measurability of allocation and payments, and joint integrability of payments, as hypotheses: they are what makes the identities `mathbb E=∈tmathbb E_xi` of the printed proof meaningful. -/
theorem observation_2_11 {n m : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (κ : Kernel Ξ Ω) [IsMarkovKernel κ]
    (M : Ξ → Mechanism n m Ω) (hM : (Mechanism.mixture M).Measurable)
    (hp : (Mechanism.mixture M).PayMeasurable)
    (hint : ∀ v, IsProfile v → ∀ i, Integrable (fun ω => (Mechanism.mixture M).pay v ω i) (μ.compProd κ)) :
    ((∀ᵐ ξ ∂μ, (M ξ).IsTIE (κ ξ)) → (Mechanism.mixture M).IsTIE (μ.compProd κ)) ∧
    ((∀ᵐ ξ ∂μ, (M ξ).IsExPostIR (κ ξ)) → (Mechanism.mixture M).IsExPostIR (μ.compProd κ)) := by sorry

end LipStableCA
