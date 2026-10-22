-- Prove2me | Theorems.Thm_NoonAmp_Symmetric_eq_12
-- name    : NoonAmp.Symmetric.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:35.926137+00:00
-- url     : https://prove2.me/theorems/892ba0e0-fe84-4997-930d-ef1c0f315ec2
-- title:
--   (11)–(12), p. 2 — NOON input as photon-added vacuum and its Q function $Q_{in}(\alpha,\beta)=|\alpha^N+\beta^N|^2e^{-(|\alpha|^2+|\beta|^2)}/(2N!\pi^2)$
-- statement:
--   Let $N\ge1$ be an integer and let $\rho_{\mathrm{in}} = |\mathrm{NOON}\rangle\langle\mathrm{NOON}|$ with $|\mathrm{NOON}\rangle = \tfrac1{\sqrt2}(|N,0\rangle + |0,N\rangle)$ on two-mode Fock space, $\rho_0 = |0,0\rangle\langle0,0|$.
--
--   1. $\rho_{\mathrm{in}}$ is a bounded operator with the matrix $\tfrac12\big[|N,0\rangle\langle N,0| + |N,0\rangle\langle 0,N| + |0,N\rangle\langle N,0| + |0,N\rangle\langle 0,N|\big]$, and it is a density operator (trace class, self-adjoint, positive, trace $1$).
--   2. Its matrix equals the photon-added vacuum form of (11):
--   $$\rho_{\mathrm{in}} = \frac{1}{2N!}\big[a^{\dagger N}\rho_0a^N + a^{\dagger N}\rho_0b^N + b^{\dagger N}\rho_0a^N + b^{\dagger N}\rho_0b^N\big].$$
--   3. Every two-mode coherent state $|\alpha,\beta\rangle$ exists as a unit vector, and the Q function of the input is
--   $$Q_{\mathrm{in}}(\alpha,\beta) \equiv \frac1{\pi^2}\langle\alpha,\beta|\rho_{\mathrm{in}}|\alpha,\beta\rangle = \frac{1}{2N!\pi^2}\,\big|\alpha^N+\beta^N\big|^2\exp\!\big[-(|\alpha|^2+|\beta|^2)\big]\qquad(\alpha,\beta\in\mathbb C).$$
--
--   This is the phase-space description of the input with which the paper starts its computation of the amplified state: the output Q function (13) is obtained from it by the scaling (7).
--
--   **Formalization Note** $N\ge1$ is added: at $N=0$ the vector (1) is $\sqrt2|0,0\rangle$, which is not normalized. The operators $a^{\dagger N}$, $a^N$ act on matrices as index shifts with factor $\sqrt{r!/(r-N)!}$ (see the definitions module). The Q function carries the paper's factor $1/\pi$ per mode; its value is the real part of $\langle\alpha,\beta|\rho|\alpha,\beta\rangle$. Matrix realization, the density property and existence of the coherent states are conclusions.
-- source:
--   Agarwal, Chaturvedi, Rai, Amplification of NOON States, arXiv:0912.5134v1, p. 2, (11), (12)

import Mathlib
import Definitions.Def_NoonAmp_Symmetric_Model

open QAlgorithms.Papers.Independent.Dependency50.P39

namespace NoonAmp.Symmetric

theorem eq_12 (N : ℕ) (hN : 1 ≤ N) :
    HasBipartiteMatrix (noonDensity N) (noonMatrix N) ∧ IsBipartiteDensity (noonDensity N) ∧
    (∀ p q : ℕ × ℕ, noonMatrix N p q =
      (((2 * (N.factorial : ℝ))⁻¹ : ℝ) : ℂ) *
        (lowerA N (raiseA N (pairDyad (0, 0) (0, 0))) p q +
          lowerB N (raiseA N (pairDyad (0, 0) (0, 0))) p q +
          lowerA N (raiseB N (pairDyad (0, 0) (0, 0))) p q +
          lowerB N (raiseB N (pairDyad (0, 0) (0, 0))) p q)) ∧
    CoherentPairRealized ∧
    ∀ α β : ℂ, husimiQ2 (noonDensity N) α β =
      (2 * (N.factorial : ℝ) * Real.pi ^ 2)⁻¹ * Complex.normSq (α ^ N + β ^ N) *
        Real.exp (-(Complex.normSq α + Complex.normSq β)) := by sorry

end NoonAmp.Symmetric
