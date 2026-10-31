-- Prove2me | Theorems.Thm_MarginalDRO_Lagrange_proof_thm2_kantorovich
-- name    : MarginalDRO.Lagrange.proof_thm2_kantorovich
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:43.057041+00:00
-- url     : https://prove2.me/theorems/83854d69-c42f-4d7a-8058-c9dca890bff6
-- title:
--   Proof of Theorem 2, pp. ec3–ec4 — Kantorovich duality for the cost c·x on ℝ × 𝒳_i, with the coupling maximum attained
-- statement:
--   Let $\mu_1,\dots,\mu_n$ be probability measures on $\mathbb R$ with finite variance, $\mathcal X \subset \mathbb R^n$ a nonempty finite set, $\nu \in \mathcal P(\mathcal X)$ and $i \in \{1,\dots,n\}$. Then there is a real number $m$ such that:
--
--   1. the maximum of $E_{(c,x)\sim\gamma}[c\,x]$ over couplings $\gamma \in \Gamma(\mu_i, \Pi_i\nu)$ exists and equals $m$;
--   2. $m$ is the infimum of $\int \varphi\, d\mu_i + \int \psi\, d\Pi_i\nu$ over pairs $(\varphi,\psi)$ with $\varphi$ $\mu_i$-integrable and $\varphi(c) + \psi(a) \ge c\,a$ for all $c \in \mathbb R$, $a \in \mathcal X_i$;
--   3. $m$ is the infimum over $\psi$ of the reduced dual
--   $$\int \psi\, d\Pi_i\nu + \int \max_{a \in \mathcal X_i}\{c\,a - \psi(a)\}\, d\mu_i(c).$$
--
--   In display form,
--   $$\max_{\gamma \in \Gamma(\mu_i,\Pi_i\nu)} E_\gamma[c\,x] = \inf_{\varphi(c)+\psi(a)\ge c a} \int \varphi\, d\mu_i + \int \psi\, d\Pi_i\nu = \inf_{\psi} \int \psi\, d\Pi_i\nu + \int \max_{a\in\mathcal X_i}\{c a - \psi(a)\}\,d\mu_i .$$
--
--   This is the specialization of Kantorovich duality (Theorem 1 of the paper) used in the proof of Theorem 2 to pass from the coupling form to the Lagrangian form, one coordinate at a time.
--
--   **Formalization Note** The potentials are real-valued (the paper allows values in $(-\infty,\infty]$); the infima are stated with `IsGLB`, so no junk value can decide them. $\int\psi\,d\Pi_i\nu$ is written as $\sum_{x\in\mathcal X}\nu(x)\psi(x_i)$.
-- source:
--   Chen, Ma, Natarajan, Simchi-Levi & Yan, preprint (2018), pp. ec3–ec4 (PDF 51–52), proof of Theorem 2, application of Theorem 1 (p. 13)

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model

open MeasureTheory ProbabilityTheory

namespace MarginalDRO.Lagrange

/-- Proof of Theorem 2, pp. ec3–ec4: Theorem 1 specialized to the cost `c x` on `ℝ × 𝒳_i`. -/
theorem proof_thm2_kantorovich {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hvar : ∀ i, MemLp id 2 (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ν : 𝒳 → ℝ) (hν : ν ∈ stdSimplex ℝ 𝒳) (i : Fin n) :
    ∃ m : ℝ,
      IsGreatest {s | ∃ γ ∈ couplings (μ i) (margMeasure 𝒳 ν i), s = ∫ p, p.1 * p.2 ∂γ} m ∧
      IsGLB {s | ∃ φ ψ : ℝ → ℝ, Integrable φ (μ i) ∧
        (∀ c : ℝ, ∀ a ∈ proj 𝒳 i, c * a ≤ φ c + ψ a) ∧
        s = ∫ c, φ c ∂(μ i) + ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i)} m ∧
      IsGLB (Set.range fun ψ : ℝ → ℝ =>
        ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i) + ∫ c, conj 𝒳 h𝒳 ψ i c ∂(μ i)) m := by sorry
end MarginalDRO.Lagrange
