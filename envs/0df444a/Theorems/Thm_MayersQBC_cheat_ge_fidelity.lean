-- Prove2me | Theorems.Thm_MayersQBC_cheat_ge_fidelity
-- name    : MayersQBC.cheat_ge_fidelity
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:26:22.118182+00:00
-- url     : https://prove2.me/theorems/043aaf2c-fc3c-4e2e-94d9-065a6785fb04
-- title:
--   Section e, p.4 — per transcript, some unitary on Alice's side gives $p_\gamma \ge F'(\gamma)$
-- statement:
--   Let $A$ and $B$ be finite-dimensional systems (Alice's and Bob's sides), $\psi_0, \psi_1$ unit vectors of $A\otimes B$ (the states $\psi'_{0,\gamma}, \psi'_{1,\gamma}$ after commit′), and $E$ an effect on $A \otimes B$ (the outcome "the honest unveil of $1$ returns $1$") that accepts $\psi_1$ with certainty, $\langle\psi_1|E|\psi_1\rangle = 1$ (correctness). Then there is a unitary $U$ on Alice's side $A$ such that
--
--   $$
--   p_\gamma := \big\langle\psi_0\big|(U\otimes I)^\dagger E (U \otimes I)\big|\psi_0\big\rangle \;\ge\; F\big(\rho_B(\psi_0), \rho_B(\psi_1)\big),
--   $$
--
--   where $F(\rho,\sigma) = (\operatorname{Tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho})^2$ is Jozsa's fidelity of Bob's reduced states. This is the paper's "$p_\gamma$ is greater than $f(F'(\gamma))$ for some function $f(z)$ such that $\lim_{z\to1} f(z) = 1$", with the explicit choice $f(z) = z$.
--
--   **Formalization Note** Alice's side is the first tensor factor; her unitary acts as `Matrix.kronecker U 1` and `traceLeft` gives Bob's reduced state. The honest unveil of $1$, together with Bob's verdict, is represented by an arbitrary effect $E$.
--
--   Differences from the source:
--   - generalization: p_γ > f(F′(γ)) for some function f with lim_{z→1} f(z) = 1 → p_γ ≥ F′(γ), i.e. the explicit f(z) = z with ≥; reason: it implies the printed claim: f(z) = 2z − 1 for z < 1 and f(1) = 0 gives p_γ > f(F′(γ)) for every value and lim_{z→1} f(z) = 1
--   - generalization: the honest unveil of 1 of one protocol, on the post-commit states ψ′0,γ, ψ′1,γ → any effect E on A ⊗ B accepting a unit vector ψ1 with certainty, and any unit vector ψ0; reason: the honest unveil composed with Bob's verdict is a two-outcome measurement on the post-commit system, so its outcome 1 is an effect; the protocol's case is a special case
--   - encoding: the fidelity [9] (Jozsa) F(ρ, σ) = (Tr √(√ρ σ √ρ))² → QAlgorithms.rootFidelity ρ σ ^ 2; reason: rootFidelity is Tr √(√ρ σ √ρ); its square is Jozsa's fidelity, the one the paper cites
--   - encoding: H_A ⊗ H_B with Alice's side H_A → EuclideanSpace ℂ (A × B) with Alice's side the first factor A; traceLeft gives Bob's reduced state and Alice acts by Matrix.kronecker U 1; reason: fixed ordering convention of the published traceLeft; it changes no instance
-- source:
--   Mayers, Unconditionally secure quantum bit commitment is impossible, arXiv:quant-ph/9605044v2, section e, third step, p.4 ("the probability pγ that unveil′ returns 1 on |ψ′0,γ⟩ is greater than f(F′(γ))")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
open QAlgorithms

namespace MayersQBC

/-- Mayers, arXiv:quant-ph/9605044v2, section e, third step, p.4: "Inequality 4 implies that the
probability pγ that unveil′ returns 1 on |ψ′0,γ⟩ is greater than f(F′(γ)) for some function f(z)
such that lim_{z→1} f(z) = 1 (more details are given in [12])." Let `ψ0, ψ1` be unit vectors of
`A ⊗ B` (the states `ψ′_{0,γ}`, `ψ′_{1,γ}` after commit′) and let `E` be an effect that accepts
`ψ1` with certainty (the honest unveil of `1` is correct). Then there is a unitary `U` on
Alice's side `A` such that `E` accepts `(U ⊗ I) ψ0` with probability at least
`F(ρ_B(ψ0), ρ_B(ψ1))`, Jozsa's fidelity of Bob's reduced states: `p_γ ≥ f(F′(γ))` with
`f(z) = z`.

**Formalization Note.** Alice's side `A` is the first tensor factor, so her unitary acts as
`Matrix.kronecker U 1`; `traceLeft` gives Bob's reduced state. Jozsa's fidelity is
`rootFidelity ^ 2`. The explicit `f(z) = z` and `≥` imply the page's existential: e.g.
`f(z) = 2z − 1` for `z < 1` and `f(1) = 0` gives the strict inequality and `lim_{z→1} f(z) = 1`. -/
theorem cheat_ge_fidelity {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ψ0 ψ1 : EuclideanSpace ℂ (A × B)) (h0 : IsState ψ0) (h1 : IsState ψ1)
    (E : Matrix (A × B) (A × B) ℂ) (hE : IsEffect E) (hcorrect : effectProb E (pureDensity ψ1) = 1) :
    ∃ U ∈ Matrix.unitaryGroup A ℂ,
      rootFidelity (traceLeft (pureDensity ψ0)) (traceLeft (pureDensity ψ1)) ^ 2 ≤
        effectProb E (pureDensity (act (Matrix.kronecker U (1 : Matrix B B ℂ)) ψ0)) := by sorry

end MayersQBC
