-- Prove2me | Theorems.Thm_OptLocalHamSim_lemma_10
-- name    : OptLocalHamSim.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:33:38.195222+00:00
-- url     : https://prove2.me/theorems/2a30806b-fcd0-4c9f-835f-49e3a41fcc81
-- title:
--   Lemma 10 — $\|\hat A_Q-U\|\le(e^{1/8}+2)\xi^{-Q}$ and coefficient bounds
-- statement:
--   Let $(c_\lambda,\omega_\lambda,P_\lambda)_{\lambda<A}$ be a table with $A\ge1$, unitary $P_\lambda$, $|c_\lambda|\le c_*$, $|\omega_\lambda|\le\omega_*$, $c_*,\omega_*\ge1$; let $C$ be unitary, $r\ge1$, $Q\ge p+1$, $h>0$, $t_\omega:=\omega_*h$, and let $E$ solve (25) with $K$ of the form (26); put $U:=[CE(h)]^r$. For $\xi>1$ with $t_\omega\xi<1$ let
--
--   $$
--   A(\xi):=\frac{c_*Ah\,t_\omega^p\xi^{p+1}}{p!\,(1-t_\omega\xi)} .
--   $$
--
--   1. If $rA(\xi)\le1/8$, then $\|\hat A_Q-U\|\le(e^{1/8}+2)\,\xi^{-Q}$.
--   2. If also $t_\omega\xi\le1/2$, then for every $J,b\in\mathbb N$, every $\lambda$ and every $0\le\beta<m$:
--
--   $$
--   |f(J)|\le1,\qquad|\gamma(b)|\le1,\qquad\xi^{p+1}|\chi_\lambda|<\tfrac12,\qquad\xi^{2^\beta}|z_{\lambda,\beta}|\le1,
--   $$
--
--   and in particular $|\chi_\lambda|\le1$ and $|z_{\lambda,\beta}|\le1$.
--
--   The first bound makes the LCU error exponentially small in $Q$; the second makes every coefficient factor implementable by the phase-average gates of eq. (12).
--
--   Differences from the source:
--   - generalization: U = e^{−iH_blk τ} = [C(h)E(h)]^r with the formula C(h) and the table of Lemma 7 → any unitary C, any table with unitary P_λ, and any E solving (25)–(26); U := (C·E(h))^r; reason: the proof uses only these properties; the source's objects satisfy them
--   - encoding: the table of A entries, padded to a power of two → A ≥ 1; reason: the uniform address probability 1/A is undefined for A = 0; a padded table is nonempty
--   - encoding: ξ^{−Q} → 1/ξ^Q; reason: the same number
--   - reading: |f(J)| ≤ 1, |γ(b)| ≤ 1, ξ^{p+1}|χ_λ| < 1/2, ξ^{2^β}|z_{λ,β}| ≤ 1 → for all J, b ∈ ℕ, all λ and all 0 ≤ β < m; reason: the source does not restrict J, b; the factors are evaluated on every register value (p.20: "bounded on every register value")
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), Lemma 10, eqs. (56)–(58), p.22

import Mathlib
import Definitions.Def_OptLocalHamSim_LCUData

open scoped Matrix.Norms.L2Operator

namespace OptLocalHamSim

/-- **Lemma 10 (Approximation error and coefficient bounds)**, Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission (held version, sha256 44a9768a…), p.22. For ξ > 1 with t_ωξ < 1,
define A(ξ) := c∗Ah t_ω^p ξ^{p+1}/(p!(1 − t_ωξ)) (56). If rA(ξ) ≤ 1/8, the approximation error
satisfies ‖Â_Q − U‖ ≤ (e^{1/8} + 2)ξ^{−Q} (57). If also t_ωξ ≤ 1/2, the coefficient factors satisfy
|f(J)| ≤ 1, |γ(b)| ≤ 1, ξ^{p+1}|χ_λ| < 1/2, ξ^{2^β}|z_{λ,β}| ≤ 1 (58). In particular, all unweighted
factors used by the circuit have modulus at most one.

**Formalization Note**
* Abstract form: any table with unitary `P_λ`, `|c_λ| ≤ c∗`, `|ω_λ| ≤ ω∗`, `c∗, ω∗ ≥ 1`, any unitary
  `C` in place of `C(h)`, and any `E` solving (25)–(26); `U := (C E(h))^r` (the paper's
  `U = e^{−iH_blk τ} = [C(h)E(h)]^r`, p.12). Standing: `r ≥ 1`, `Q ≥ p + 1`, `h > 0`, `A ≥ 1`.
* (58) is stated for every register value `J, b ∈ ℕ`, every entry `λ`, and every `0 ≤ β < m`;
  "in particular" is `|χ_λ| ≤ 1` and `|z_{λ,β}| ≤ 1`. -/
theorem lemma_10 {n : Type} [Fintype n] [DecidableEq n] (d : LCUData n) (hA : 0 < d.A)
    (hr : 1 ≤ d.r) (hQ : d.p + 1 ≤ d.Q) (hh : 0 < d.h) (hcs : 1 ≤ d.cs) (hωs : 1 ≤ d.ωs)
    (hc : ∀ l, ‖d.c l‖ ≤ d.cs) (hω : ∀ l, |d.ω l| ≤ d.ωs)
    (hC : d.C ∈ Matrix.unitaryGroup n ℂ) (hP : ∀ l, d.P l ∈ Matrix.unitaryGroup n ℂ)
    (E : ℝ → Matrix n n ℂ) (hE : SolvesResidual d.c d.ω d.P d.p E)
    (ξ : ℝ) (hξ : 1 < ξ) (htξ : d.tω * ξ < 1) :
    (d.r * d.Aξ ξ ≤ 1 / 8 →
      ‖d.AhatQ - (d.C * E d.h) ^ d.r‖ ≤ (Real.exp (1 / 8) + 2) / ξ ^ d.Q) ∧
    (d.r * d.Aξ ξ ≤ 1 / 8 → d.tω * ξ ≤ 1 / 2 →
      (∀ J : ℕ, |d.fJ J| ≤ 1) ∧ (∀ b : ℕ, |d.gam b| ≤ 1) ∧
      (∀ l, ξ ^ (d.p + 1) * ‖d.χ l‖ < 1 / 2) ∧
      (∀ l, ∀ β < d.m, ξ ^ (2 ^ β) * ‖d.zfac l β‖ ≤ 1) ∧
      (∀ l, ‖d.χ l‖ ≤ 1) ∧ (∀ l, ∀ β < d.m, ‖d.zfac l β‖ ≤ 1)) := by sorry

end OptLocalHamSim
