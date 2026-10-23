-- Prove2me | Theorems.Thm_IntuitiveDPI_Smooth_lemma_5_6
-- name    : IntuitiveDPI.Smooth.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:41.926011+00:00
-- url     : https://prove2.me/theorems/6004f1cb-5786-4a26-8dfc-d529ac78df69
-- title:
--   Lemma 5.6, p. 7 — ∃ ρ̃ ∈ B^ε(ρ) with H_min^ε(A|B)_ρ ≤ H(A|B)_ρ̃
-- statement:
--   Let $\rho=\rho_{AB}$ be a density matrix on $\mathcal H_A\otimes\mathcal H_B$ and $0\le\varepsilon<1$. Then there is a subnormalized $\tilde\rho\in\mathcal B^\varepsilon(\rho)$ such that
--   $$H^\varepsilon_{\min}(A|B)_\rho\le H(A|B)_{\tilde\rho},$$
--   where for a subnormalized $\tilde\rho$ the conditional von Neumann entropy is (36):
--   $$H(A|B)_{\tilde\rho}=\frac{1}{\operatorname{Tr}\tilde\rho_{AB}}\max_{\sigma_B}\operatorname{Tr}\bigl(\tilde\rho_{AB}(\log(\mathbb 1_A\otimes\sigma_B)-\log\tilde\rho_{AB})\bigr).$$
--
--   The smooth min-entropy is thus bounded by the von Neumann entropy of a nearby state; applied to $\rho^{\otimes n}$ and combined with Lemma B.1 it gives the upper half of the QAEP (Lemma 4.2).
--
--   **Formalization Note** The range $0\le\varepsilon<1$ is added: for $\varepsilon<0$ the ball is empty and no $\tilde\rho$ exists, and for $\varepsilon\ge1$ the ball contains $0$, so $H^\varepsilon_{\min}(A|B)_\rho=+\infty$ and no real number bounds it (and $\operatorname{Tr}\tilde\rho=0$ in (36)). The paper only uses $\varepsilon\to0$. $H(A|B)_{\tilde\rho}$ is `condEntropySub`, whose maximum is taken over positive definite density matrices $\sigma_B$ (see the definitions module); it is not P67's `conditionalEntropy`, which is $H(AB)-H(B)$ and differs from (36) for subnormalized states.
-- source:
--   Beaudry & Renner, An intuitive proof of the data processing inequality, arXiv:1107.0740v2, p. 7, Lemma 5.6, (35), (36)

import Mathlib
import Definitions.Def_IntuitiveDPI_Smooth_Basic

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB renyiEntropy)
open scoped ComplexOrder Matrix
open Filter Topology

namespace IntuitiveDPI.Smooth

/-- Lemma 5.6, (35), p. 7: for a density matrix `ρ` on `A ⊗ B` and `0 ≤ ε < 1` there is
`ρ' = ρ̃` in the ball `B^ε(ρ)` with `H^ε_min(A|B)_ρ ≤ H(A|B)_ρ̃`, the conditional entropy (36) of the
subnormalized `ρ̃`. -/
theorem lemma_5_6 {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ∃ ρ' : Matrix (A × B) (A × B) ℂ, IsSubnormalized ρ' ∧ purifiedDistance ρ' ρ ≤ ε ∧
      smoothConditionalMinEntropy ρ ε ≤ ((condEntropySub ρ' : ℝ) : EReal) := by sorry

end IntuitiveDPI.Smooth
