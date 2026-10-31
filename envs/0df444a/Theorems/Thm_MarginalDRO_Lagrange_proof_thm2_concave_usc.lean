-- Prove2me | Theorems.Thm_MarginalDRO_Lagrange_proof_thm2_concave_usc
-- name    : MarginalDRO.Lagrange.proof_thm2_concave_usc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:32.528109+00:00
-- url     : https://prove2.me/theorems/76dc1a9a-8b1d-4e1c-963f-92d9290673a9
-- title:
--   Proof of Theorem 2, pp. ec3–ec4 — ν ↦ max_{γ∈Γ(µ_i,Π_iν)} E[c̃_i x_i] is concave and upper semicontinuous on 𝒫(𝒳)
-- statement:
--   Let $\mu_1,\dots,\mu_n$ be probability measures on $\mathbb R$ with finite variance, $\mathcal X \subset \mathbb R^n$ finite and $i \in \{1,\dots,n\}$. Then the function
--   $$\nu \longmapsto \sup_{\gamma \in \Gamma(\mu_i,\Pi_i\nu)} E_{(c,x)\sim\gamma}[c\,x]$$
--   is concave and upper semicontinuous on the simplex $\mathcal P(\mathcal X)$.
--
--   This is what makes the outer maximum over $\nu$ in Theorem 2 attained: an upper semicontinuous function on the compact set $\mathcal P(\mathcal X)$ attains its maximum.
--
--   **Formalization Note** The supremum is a real `sSup`. For $\nu \in \mathcal P(\mathcal X)$ the set of coupling values is nonempty (the independent coupling) and bounded above by $\max_{a\in\mathcal X_i}|a|\int|c|\,d\mu_i$, which is finite under the finite-variance hypothesis, so the supremum is the true one; it is attained by the Kantorovich milestone. For finite $\mathcal X$ the weak-* topology on $\mathcal P(\mathcal X)$ is the Euclidean topology on the simplex.
-- source:
--   Chen, Ma, Natarajan, Simchi-Levi & Yan, preprint (2018), pp. ec3–ec4 (PDF 51–52), proof of Theorem 2

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model

open MeasureTheory ProbabilityTheory

namespace MarginalDRO.Lagrange

/-- Proof of Theorem 2, pp. ec3–ec4: `ν ↦ max_{γ_i ∈ Γ(µ_i, Π_iν)} E[c̃_i x_i]` is concave and
upper semicontinuous on `𝒫(𝒳)`. -/
theorem proof_thm2_concave_usc {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hvar : ∀ i, MemLp id 2 (μ i)) (𝒳 : Finset (Fin n → ℝ)) (i : Fin n) :
    ConcaveOn ℝ (stdSimplex ℝ 𝒳) (fun ν => couplingValue (μ i) (margMeasure 𝒳 ν i)) ∧
      UpperSemicontinuousOn (fun ν => couplingValue (μ i) (margMeasure 𝒳 ν i))
        (stdSimplex ℝ 𝒳) := by sorry
end MarginalDRO.Lagrange
