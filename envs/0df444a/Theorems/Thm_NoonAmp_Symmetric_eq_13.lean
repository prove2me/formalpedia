-- Prove2me | Theorems.Thm_NoonAmp_Symmetric_eq_13
-- name    : NoonAmp.Symmetric.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:43.243906+00:00
-- url     : https://prove2.me/theorems/60968480-b535-4e78-99f2-60c0f57a2755
-- title:
--   (13), p. 2 — Q function of the symmetrically amplified NOON state: $Q_{out}(\alpha,\beta)=G^{-4}Q_{in}(\alpha/G,\beta/G)$
-- statement:
--   Let $N\ge1$, $G>1$, let $\rho_{\mathrm{in}}$ be the NOON density of (11), and let $A_\ell(G)$ be the Kraus operators of the quantum-limited amplifier of amplitude gain $G$, $\langle n+\ell|A_\ell(G)|n\rangle = G^{-1}\sqrt{\binom{n+\ell}{\ell}}(1-G^{-2})^{\ell/2}G^{-n}$. Then:
--
--   1. every $A_\ell(G)\otimes A_{\ell'}(G)$ is a bounded operator with the product matrix, $\rho_{\mathrm{in}}$ is realized, and all two-mode coherent states $|\alpha,\beta\rangle$ exist as unit vectors;
--   2. the series $\sum_{\ell,\ell'}(A_\ell\otimes A_{\ell'})\rho_{\mathrm{in}}(A_\ell\otimes A_{\ell'})^\dagger$ converges in trace norm to a density operator $\rho_{\mathrm{out}}$;
--   3. for all $\alpha,\beta\in\mathbb C$, with $Q(\alpha,\beta) = \pi^{-2}\langle\alpha,\beta|\cdot|\alpha,\beta\rangle$,
--   $$Q_{\mathrm{out}}(\alpha,\beta) = \frac1{G^4}\,Q_{\mathrm{in}}(\alpha/G,\beta/G) = \frac{1}{2N!\pi^2G^{2N+4}}\,\big|\alpha^N+\beta^N\big|^2\exp\!\big[-(|\alpha|^2+|\beta|^2)/G^2\big].$$
--
--   The first equality is the two-mode form of the single-mode scaling law (7); the second is its evaluation on (12). The paper derives the output density (14) from this Q function.
--
--   **Formalization Note** The channel is the quantum-limited amplifier in Kraus form, whose single-mode Q action is (7) (the open platform theorem `Dependency50.P39.amplifierHusimiScaling`); the paper's master equation (2) at $\eta\to0$ is not formalized. $N\ge1$ (normalization of (1)) and $G>1$ (the paper's $G=e^{(N_1-N_2)\kappa t}>1$) are added. Realization, trace-norm convergence and the density property of the output are conclusions.
-- source:
--   Agarwal, Chaturvedi, Rai, Amplification of NOON States, arXiv:0912.5134v1, p. 2, (13) (with (7))

import Mathlib
import Definitions.Def_NoonAmp_Symmetric_Model

open QAlgorithms.Papers.Independent.Dependency50.P39

namespace NoonAmp.Symmetric

theorem eq_13 (N : ℕ) (hN : 1 ≤ N) (G : ℝ) (hG : 1 < G) :
    SymAmpRealized G ∧ HasBipartiteMatrix (noonDensity N) (noonMatrix N) ∧
    CoherentPairRealized ∧
    ∃ Y : BipartiteOperator,
      TraceHasSum (fun l : ℕ × ℕ => bipartiteKrausTerm (symAmpKraus G l) (noonDensity N)) Y ∧
      IsBipartiteDensity Y ∧
      ∀ α β : ℂ,
        husimiQ2 Y α β = (G ^ 4)⁻¹ * husimiQ2 (noonDensity N) (α / (G : ℂ)) (β / (G : ℂ)) ∧
        husimiQ2 Y α β =
          (2 * (N.factorial : ℝ) * Real.pi ^ 2 * G ^ (2 * N + 4))⁻¹ *
            Complex.normSq (α ^ N + β ^ N) *
            Real.exp (-(Complex.normSq α + Complex.normSq β) / G ^ 2) := by sorry

end NoonAmp.Symmetric
