-- Prove2me | Theorems.Thm_MayersQBC_reduced_states_same_positive_spectrum
-- name    : MayersQBC.reduced_states_same_positive_spectrum
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:26:10.445125+00:00
-- url     : https://prove2.me/theorems/a196be58-06ea-4ae9-aafd-f260ba60528b
-- title:
--   Section e, p.4 — the two reduced states of a pure state share their positive eigenvalues with multiplicity
-- statement:
--   Let $A$ and $B$ be finite-dimensional systems (Alice's and Bob's sides) and let $\psi$ be a vector of $A \otimes B$. Let $\rho_A(\psi) = \operatorname{Tr}_B|\psi\rangle\langle\psi|$ and $\rho_B(\psi) = \operatorname{Tr}_A|\psi\rangle\langle\psi|$ be its two reduced states. Then for every real $\mu > 0$,
--
--   $$
--   \dim \ker\big(\rho_A(\psi) - \mu I\big) = \dim \ker\big(\rho_B(\psi) - \mu I\big),
--   $$
--
--   that is, $\rho_A(\psi)$ and $\rho_B(\psi)$ have the same positive eigenvalues with the same multiplicity.
--
--   In the proof of the perfectly concealing case, applied to $\psi'_{0,\gamma}$ and $\psi'_{1,\gamma}$, whose Bob states coincide, it gives the paper's statement that $\rho_B$, $\rho_A(\psi'_{0,\gamma})$ and $\rho_A(\psi'_{1,\gamma})$ share their positive eigenvalues; the paper derives it from the Schmidt decomposition.
--
--   **Formalization Note** `traceRight` traces out the second factor (Bob) and gives $\rho_A$; `traceLeft` traces out the first factor (Alice) and gives $\rho_B$. The multiplicity of $\mu$ is the dimension of its eigenspace.
--
--   Differences from the source:
--   - generalization: the three density matrices ρB, ρA(|ψ′0,γ⟩), ρA(|ψ′1,γ⟩), with ρB shared by both states → the two reduced states of one vector ψ; reason: applying the statement to ψ′0,γ and to ψ′1,γ, whose Bob states are both ρB, gives the three-matrix claim
--   - generalization: the pure states |ψ′b,γ⟩ (unit vectors) → any vector ψ of A ⊗ B; reason: unit vectors are a special case
--   - encoding: multiplicity of the eigenvalue → Module.finrank of the eigenspace of Matrix.toLin'; reason: the reduced states are Hermitian, so geometric and algebraic multiplicities agree
--   - encoding: H_A ⊗ H_B with Alice's side H_A → EuclideanSpace ℂ (A × B) with Alice's side the first factor A; traceLeft gives Bob's reduced state and Alice acts by Matrix.kronecker U 1; reason: fixed ordering convention of the published traceLeft; it changes no instance
-- source:
--   Mayers, Unconditionally secure quantum bit commitment is impossible, arXiv:quant-ph/9605044v2, section e, third step, p.4 ("these three density matrices share the same positive eigenvalues with the same multiplicity")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
open QAlgorithms

namespace MayersQBC

/-- Mayers, arXiv:quant-ph/9605044v2, section e, third step, p.4: "In the above formula, λi are
eigenvalues of the three density matrices ρB, ρA(|ψ′0,γ⟩) and ρA(|ψ′1,γ⟩). The fact that these
three density matrices share the same positive eigenvalues with the same multiplicity is a
direct consequence of the Schmidt decomposition theorem [8,14]." For every vector `ψ` of
`A ⊗ B`, Alice's reduced state `ρ_A(ψ) = Tr_B |ψ⟩⟨ψ|` and Bob's reduced state
`ρ_B(ψ) = Tr_A |ψ⟩⟨ψ|` have the same positive eigenvalues with the same multiplicity: for every
real `μ > 0`, the `μ`-eigenspaces of the two matrices have the same dimension.

**Formalization Note.** Alice's side `A` is the first tensor factor: `traceRight` traces out
Bob's side and gives `ρ_A`, `traceLeft` traces out Alice's side and gives `ρ_B`. The
multiplicity of `μ` is the dimension of its eigenspace (geometric multiplicity; it equals the
algebraic one for these Hermitian matrices). The page's three-matrix claim (ρ_B shared by
ψ′_{0,γ} and ψ′_{1,γ}) is this statement applied to both states. `ψ` need not be a unit
vector. -/
theorem reduced_states_same_positive_spectrum {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (ψ : EuclideanSpace ℂ (A × B)) (μ : ℝ) (hμ : 0 < μ) :
    Module.finrank ℂ
        (Module.End.eigenspace (Matrix.toLin' (traceRight (pureDensity ψ))) (μ : ℂ)) =
      Module.finrank ℂ
        (Module.End.eigenspace (Matrix.toLin' (traceLeft (pureDensity ψ))) (μ : ℂ)) := by sorry

end MayersQBC
