-- Prove2me | Theorems.Thm_OptLocalHamSim_lemma_9
-- name    : OptLocalHamSim.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:33:53.375572+00:00
-- url     : https://prove2.me/theorems/151c204f-e130-44a9-ad7e-694d69cf1b79
-- title:
--   Lemma 9 — low-degree matching: the terms of $\hat A_Q$ with $d(z)\le Q$ sum to $A_Q=\sum_{|\Gamma|\le Q}d_\Gamma W_\Gamma$
-- statement:
--   Let $(c_\lambda,\omega_\lambda,P_\lambda)_{\lambda<A}$ be a table with $A\ge1$, $C$ a matrix, $r\ge1$, $Q\ge p+1$, $h>0$ and $c_*,\omega_*\ge1$, and form the label LCU of §3.3. Then
--
--   $$
--   \sum_{z:\,d(z)\le Q}2\pi(z)\Bigl(\prod_{u=0}^{N-1}\zeta_u(z)\Bigr)W_z=A_Q:=\sum_{|\Gamma|\le Q}d_\Gamma W_\Gamma .
--   $$
--
--   Thus the finite LCU $\hat A_Q$ of eq. (53) agrees with the exact path expansion of $[CE(h)]^r$ through degree $Q$; the two differ only in their high-degree tails, which Lemma 10 bounds.
--
--   Differences from the source:
--   - generalization: the table of Lemma 7 and the product-formula step C(h) → any table with arbitrary matrices P_λ and any matrix C; reason: the identity is algebraic and uses no property of P_λ or C
--   - encoding: the table of A entries, padded to a power of two → A ≥ 1; reason: the uniform address probability 1/A is undefined for A = 0; a padded table is nonempty
--   - encoding: paths Γ with |Γ| ≤ Q → paths with at most Q insertions per microstep and degrees at most Q, filtered by q ≥ p and |Γ| ≤ Q; reason: every path with |Γ| ≤ Q has this form, uniquely
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), Lemma 9, eqs. (53)–(55), p.21

import Mathlib
import Definitions.Def_OptLocalHamSim_LCUData

namespace OptLocalHamSim

/-- **Lemma 9 (Low-degree matching)**, Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission (held version, sha256 44a9768a…), p.21. The terms in Eq. (53) with insertion degree
d(z) ≤ Q sum to the truncated path expansion A_Q := ∑_{|Γ|≤Q} d_Γ W_Γ (54).

**Formalization Note** Stated for any table `(c_λ, ω_λ, P_λ)` with arbitrary matrices `P_λ` and any
matrix `C` in place of `C(h)`; the hypotheses are the standing ones of §3.3: `r ≥ 1`,
`Q ≥ p + 1`, `h > 0`, `c∗, ω∗ ≥ 1` (Lemma 7), and a nonempty table (`A ≥ 1`, as after padding to a
power of two). The terms of (53) are `2π(z)(∏_u ζ_u(z)) W_z` (`LCUData`). -/
theorem lemma_9 {n : Type} [Fintype n] [DecidableEq n] (d : LCUData n) (hA : 0 < d.A)
    (hr : 1 ≤ d.r) (hQ : d.p + 1 ≤ d.Q) (hh : 0 < d.h) (hcs : 1 ≤ d.cs) (hωs : 1 ≤ d.ωs) :
    ∑ z ∈ Finset.univ.filter (fun z : d.Label => d.deg z ≤ d.Q),
        (((2 * d.prob z : ℝ) : ℂ) * ∏ u, d.ζ z u) • d.Wz z = d.AQ := by sorry

end OptLocalHamSim
