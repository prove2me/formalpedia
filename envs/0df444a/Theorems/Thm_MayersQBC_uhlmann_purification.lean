-- Prove2me | Theorems.Thm_MayersQBC_uhlmann_purification
-- name    : MayersQBC.uhlmann_purification
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:26:20.21691+00:00
-- url     : https://prove2.me/theorems/61ac1747-b3f0-493c-a17c-dde8a96ad6d3
-- title:
--   Display (4), p.4 — Uhlmann: a purification $\psi_{01}$ of $\rho_B(\psi'_{0,\gamma})$ with $\langle\psi_{01}|\psi'_{1,\gamma}\rangle = \sqrt{F'(\gamma)}$
-- statement:
--   Let $A$ and $B$ be finite-dimensional systems and $\psi_0, \psi_1$ unit vectors of $A \otimes B$, with Bob's reduced states $\rho_B(\psi_b) = \operatorname{Tr}_A|\psi_b\rangle\langle\psi_b|$. Then there is a unit vector $\psi_{01}$ of $A\otimes B$ that is a purification of $\rho_B(\psi_0)$, i.e. $\rho_B(\psi_{01}) = \rho_B(\psi_0)$, such that
--
--   $$
--   \langle \psi_{01} | \psi_1 \rangle = \operatorname{Tr}\sqrt{\sqrt{\rho_B(\psi_0)}\,\rho_B(\psi_1)\sqrt{\rho_B(\psi_0)}} = \sqrt{F\big(\rho_B(\psi_0), \rho_B(\psi_1)\big)} ,
--   $$
--
--   a real number. Since $0 \le \sqrt F \le 1$, this gives the paper's inequality (4), $\langle\psi_{01}|\psi'_{1,\gamma}\rangle \ge F'(\gamma)$, for $\psi_b = \psi'_{b,\gamma}$.
--
--   This is the attained form of Uhlmann's theorem on a fixed purifying system: the purification lives on the same Alice side on which $\psi_0$ and $\psi_1$ live, so Alice can reach it from $\psi_0$ by a unitary on her side.
--
--   **Formalization Note** $\langle x|y\rangle$ is `inner ℂ x y`, conjugate-linear in $x$. Alice's side is the first tensor factor and `traceLeft` gives $\rho_B$. The overlap is equated with `rootFidelity`, the square root of Jozsa's fidelity $F$.
--
--   Differences from the source:
--   - generalization: ⟨ψ01|ψ′1,γ⟩ ≥ F′(γ) (4) → inner ℂ ψ01 ψ1 = rootFidelity ρB(ψ0) ρB(ψ1) = √F, a real number; reason: 0 ≤ √F ≤ 1, so √F ≥ F and the equality implies the printed inequality
--   - generalization: the post-commit states ψ′0,γ, ψ′1,γ → any unit vectors ψ0, ψ1 of A ⊗ B; reason: the post-commit states are a special case
--   - encoding: the fidelity [9] (Jozsa) F(ρ, σ) = (Tr √(√ρ σ √ρ))² → QAlgorithms.rootFidelity ρ σ ^ 2; reason: rootFidelity is Tr √(√ρ σ √ρ); its square is Jozsa's fidelity, the one the paper cites
--   - encoding: H_A ⊗ H_B with Alice's side H_A → EuclideanSpace ℂ (A × B) with Alice's side the first factor A; traceLeft gives Bob's reduced state and Alice acts by Matrix.kronecker U 1; reason: fixed ordering convention of the published traceLeft; it changes no instance
-- source:
--   Mayers, Unconditionally secure quantum bit commitment is impossible, arXiv:quant-ph/9605044v2, section e, third step, display (4), p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
open QAlgorithms

namespace MayersQBC

/-- Mayers, arXiv:quant-ph/9605044v2, section e, third step, display (4), p.4: "Any state |ψ01⟩ of
the overall system such that ρB(|ψ01⟩) = ρB(|ψ′0,γ⟩) is called a purification of the density
matrix ρB(|ψ′0,γ⟩). Because |ψ′1,γ⟩ is a purification of ρB(|ψ′1,γ⟩), Uhlmann's theorem [9] says
that there exists a purification |ψ01⟩ of ρB(|ψ′0,γ⟩) such that ⟨ψ01|ψ′1,γ⟩ ≥ F′(γ) (4)".
For unit vectors `ψ0, ψ1` of `A ⊗ B` there is a unit vector `ψ01` of `A ⊗ B` with the same
reduced state on Bob's side as `ψ0` whose overlap with `ψ1` is real and equals
`√F(ρ_B(ψ0), ρ_B(ψ1)) = Tr √(√ρ_B(ψ0) ρ_B(ψ1) √ρ_B(ψ0))`.

**Formalization Note.** Alice's side `A` is the first tensor factor; `traceLeft` gives Bob's
reduced state. `inner ℂ x y = ⟨x|y⟩` is conjugate-linear in `x`. The overlap is stated as an
equality with `QAlgorithms.rootFidelity` (the square root of Jozsa's fidelity `F`); since
`0 ≤ √F ≤ 1`, it implies the page's `⟨ψ01|ψ′1,γ⟩ ≥ F′(γ)`. The purifying system is the given
`A`, the one on which Alice acts. -/
theorem uhlmann_purification {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (ψ0 ψ1 : EuclideanSpace ℂ (A × B)) (h0 : IsState ψ0) (h1 : IsState ψ1) :
    ∃ ψ01 : EuclideanSpace ℂ (A × B), IsState ψ01 ∧
      traceLeft (pureDensity ψ01) = traceLeft (pureDensity ψ0) ∧
      inner ℂ ψ01 ψ1 =
        ((rootFidelity (traceLeft (pureDensity ψ0)) (traceLeft (pureDensity ψ1)) : ℝ) : ℂ) := by sorry

end MayersQBC
