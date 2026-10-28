-- Prove2me | Theorems.Thm_NechitaRDM_MP_eq_24
-- name    : NechitaRDM.MP.eq_24
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:39.908216+00:00
-- url     : https://prove2.me/theorems/27c19250-222c-43b9-99c3-dfa4cfe7d79a
-- title:
--   Eq. (24), p. 9 — the eigenvalues of ρ = W/Tr W are λᵢ/Σⱼλⱼ, where λ₁, …, λₙ are the eigenvalues of the Wishart matrix W
-- statement:
--   Let $X$ be an $n \times k$ complex matrix and $W = XX^*$. If $\lambda_1, \dots, \lambda_n$ are the eigenvalues of $W$ and $\tilde\lambda_1, \dots, \tilde\lambda_n$ those of $\rho = W/\operatorname{Tr} W$, then (as lists counted with multiplicity)
--   $$\tilde\lambda_i = \frac{\lambda_i}{\sum_{j=1}^n \lambda_j}, \qquad 1 \le i \le n .$$
--
--   This is how the spectrum of a density matrix of law $\mu_{n,k}$ is read off the spectrum of a Wishart matrix; it is used in eq. (51) of the proof of Theorem 5.
--
--   **Formalization Note** The page states it for a Wishart random matrix; since every realization of a Wishart matrix is of the form $XX^*$, it is stated for every deterministic $X$. Eigenvalues are multisets (with multiplicity). At $X = 0$ both sides are $n$ zeros in Lean (`0⁻¹ = 0`, `0 / 0 = 0`), so no hypothesis is needed.
-- source:
--   Nechita, Asymptotics of random density matrices, arXiv:quant-ph/0702154v3, p. 9, eq. (24)

import Mathlib
import Definitions.Def_NechitaRDM_MP_Basic

namespace NechitaRDM.MP

/-- **Eq. (24)** (p. 9). If `λ₁, …, λₙ` are the eigenvalues of `W = XX*` and `λ̃₁, …, λ̃ₙ` those
of `ρ = W / Tr W`, then `λ̃ᵢ = λᵢ / Σⱼ λⱼ` (as multisets). -/
theorem eq_24 {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℂ) :
    eigs ((wishart X).trace⁻¹ • wishart X) =
      (eigs (wishart X)).map (fun x => x / (eigs (wishart X)).sum) := by sorry

end NechitaRDM.MP
