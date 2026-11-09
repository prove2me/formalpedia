-- Prove2me | Theorems.Thm_HopRamsey_lemma_1_truncation
-- name    : HopRamsey.lemma_1_truncation
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:45:34.469702+00:00
-- url     : https://prove2.me/theorems/9e499ea1-651e-4e04-8097-fb87fba3fcfb
-- title:
--   Truncation step: conditioned on $\overline\Psi$ the tape is a product of truncated geometric laws
-- statement:
--   Let $(\tau_i)_{i\in I}$ be a finite family of independent geometric variables, $\tau_i$ with parameter $p_i\in(0,1]$, and let $k\ge1$. Conditioned on the event $\overline\Psi=\{\tau_i<k\text{ for all }i\}$, the variables remain independent and each has the truncated geometric law of Algorithm 2: the conditional joint law equals the product of the truncated laws, and
--
--   $$
--   \Pr[\tau_i=R\mid\overline\Psi]=\frac{(1-p_i)^R p_i}{1-(1-p_i)^k}\qquad(0\le R<k).
--   $$
--
--   This is why the tape process, conditioned on $\overline\Psi$, has exactly the law of the algorithm.
--
--   Differences from the source:
--   - generalization: the tape τ_{ℓ,i} with parameters p_ℓ and the truncation parameter k of Figure 2 → any finite index type, any parameters p_i ∈ (0,1] and any k ≥ 1; reason: the statement is a fact about independent geometric variables; the tape is an instance (0 < p_ℓ ≤ 1 under the standing assumptions)
--   - encoding: "the tape entries remain mutually independent ... and each τ_{ℓ,i} has exactly the truncated geometric distribution" → the conditioned product measure `ProbabilityTheory.cond (Measure.pi …) {∀ i, τ i < k}` equals the product of the truncated laws, plus the mass function of the truncated law on [0,k); reason: equality with a product measure is independence together with the marginals
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), proof of Lemma 1, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_HopRamsey_truncGeom

open scoped ENNReal

namespace HopRamsey

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…),
Truncation step, proof of Lemma 1, p.20 (PDF p.22): "Conditioned on Ψ̄, the tape entries remain
mutually independent (as Ψ̄ is an intersection of independent events, one per entry), and each
τ_{ℓ,i} has exactly the truncated geometric distribution of Algorithm 2:
Pr[τ_{ℓ,i} = R | Ψ̄] = (1−p_ℓ)^R·p_ℓ / (1−(1−p_ℓ)^k) for R ∈ [0,k)."

**Formalization Note.** For any finite family of independent geometric variables with parameters
`p_i ∈ (0, 1]` and any `k ≥ 1`: (1) the joint law conditioned on `Ψ̄ = {τ_i < k for all i}` is the
product of the truncated laws `truncGeom (p_i) k` (independence and the marginals at once), and
(2) the truncated law has the printed mass function on `[0, k)`. -/
theorem lemma_1_truncation {ι : Type} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 < p i ∧ p i ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ProbabilityTheory.cond (MeasureTheory.Measure.pi fun i => (geomLaw (p i)).toMeasure)
        {τ : ι → ℕ | ∀ i, τ i < k} =
      MeasureTheory.Measure.pi (fun i => (truncGeom (p i) k).toMeasure) ∧
    ∀ i, ∀ R : ℕ, R < k →
      truncGeom (p i) k R = ENNReal.ofReal ((1 - p i) ^ R * p i / (1 - (1 - p i) ^ k)) := by sorry

end HopRamsey
