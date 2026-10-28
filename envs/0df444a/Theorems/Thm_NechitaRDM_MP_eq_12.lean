-- Prove2me | Theorems.Thm_NechitaRDM_MP_eq_12
-- name    : NechitaRDM.MP.eq_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:43.268282+00:00
-- url     : https://prove2.me/theorems/f293f58e-9d68-4393-ad31-eeacd4da8376
-- title:
--   Eq. (12), p. 6 — the reduced state Tr_K |ψ⟩⟨ψ| equals XX*/Tr(XX*) for the n × k coordinate matrix X(i, j) = ψ_ij
-- statement:
--   Let $\psi = \sum_{i=1}^n\sum_{j=1}^k \psi_{ij}\, e_i \otimes f_j$ be a vector of $\mathbb C^n \otimes \mathbb C^k$ and arrange its coordinates in the $n\times k$ matrix $X$ with $X(i,j) = \psi_{ij}$. Then the partial trace over the environment $\mathbb C^k$ of the pure density matrix $|\psi\rangle\langle\psi|$ is
--   $$\rho = \operatorname{Tr}_{\mathcal K}\big(|\psi\rangle\langle\psi|\big) = \frac{X X^*}{\operatorname{Tr}(X X^*)} .$$
--
--   This deterministic identity, obtained in the paper through eqs. (9)–(11), turns a random pure state of the global system into a normalized Wishart-type matrix.
--
--   **Formalization Note** $\mathbb C^n\otimes\mathbb C^k$ is indexed by `Fin n × Fin k` and $\operatorname{Tr}_{\mathcal K}$ is the published `WildeQIT.partialTraceRight`. No hypothesis $\psi \ne 0$ is needed: at $\psi = 0$ both sides are $0$ in Lean.
-- source:
--   Nechita, Asymptotics of random density matrices, arXiv:quant-ph/0702154v3, p. 6, eq. (12) (derived through eqs. (9)–(11), pp. 5–6)

import Mathlib
import Definitions.Def_NechitaRDM_MP_Basic

namespace NechitaRDM.MP

/-- **Eq. (12)** (p. 6). Arranging the coordinates `ψ_{ij}` of `ψ ∈ ℂⁿ ⊗ ℂᵏ` in an `n × k`
matrix `X` with `X(i, j) = ψ_{ij}`, the reduced state is `Tr_K |ψ⟩⟨ψ| = XX* / Tr(XX*)`. -/
theorem eq_12 {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℂ) :
    WildeQIT.partialTraceRight (pureState fun p : Fin n × Fin k => X p.1 p.2) =
      (wishart X).trace⁻¹ • wishart X := by sorry

end NechitaRDM.MP
