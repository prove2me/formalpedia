-- Prove2me | Theorems.Thm_NoonAmp_Symmetric_amplified_noon_density
-- name    : NoonAmp.Symmetric.amplified_noon_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:37.633293+00:00
-- url     : https://prove2.me/theorems/984c74e9-5775-494e-bf7b-9a6c65b61557
-- title:
--   (17), p. 3 — number-basis density matrix of a NOON state after symmetric quantum-limited amplification with gain G
-- statement:
--   Let $|n,m\rangle$ be the number basis of two bosonic modes $a,b$, let $N\ge1$ and let
--   $$|\mathrm{NOON}\rangle = \tfrac1{\sqrt2}\big(|N,0\rangle + |0,N\rangle\big),\qquad \rho_{\mathrm{in}} = |\mathrm{NOON}\rangle\langle\mathrm{NOON}| .$$
--   For amplitude gain $G>1$ let $A_\ell(G)$, $\ell\in\mathbb N$, be the Kraus operators of the quantum-limited amplifier, $\langle n+\ell|A_\ell(G)|n\rangle = G^{-1}\sqrt{\binom{n+\ell}{\ell}}(1-G^{-2})^{\ell/2}G^{-n}$ (all other entries $0$), and let the symmetric amplifier act by
--   $$\Phi_G(\rho) = \sum_{\ell,\ell'=0}^\infty (A_\ell(G)\otimes A_{\ell'}(G))\,\rho\,(A_\ell(G)\otimes A_{\ell'}(G))^\dagger .$$
--   Then each $A_\ell(G)\otimes A_{\ell'}(G)$ is a bounded operator with the product matrix, $\rho_{\mathrm{in}}$ is a density operator, the series $\Phi_G(\rho_{\mathrm{in}})$ converges in trace norm to a density operator $\rho_{\mathrm{out}}$, and, with every entry of the double series converging,
--   $$\rho_{\mathrm{out}} = \frac{1}{2N!G^{2N+4}}\sum_{n,m=0}^\infty\Big(\frac{G^2-1}{G^2}\Big)^{n+m}\Big[\frac{(n+N)!}{n!}|n+N,m\rangle\langle n+N,m| + \frac{(m+N)!}{m!}|n,m+N\rangle\langle n,m+N| + \sqrt{\frac{(n+N)!}{n!}\frac{(m+N)!}{m!}}\big(|n+N,m\rangle\langle n,m+N| + |n,m+N\rangle\langle n+N,m|\big)\Big]$$
--   as an identity of number-basis matrices.
--
--   This is the paper's analytic density matrix of the amplified NOON state at arbitrary gain; its partial transpose (18) is the basis of the paper's entanglement analysis (Fig. 1).
--
--   **Formalization Note** The channel is the quantum-limited amplifier in Kraus form; its single-mode Q action is exactly the paper's (7), $Q_{\mathrm{out}}(\alpha) = G^{-2}Q_{\mathrm{in}}(\alpha/G)$, the $\eta\to0$ limit of the master equation (2) (open platform theorem `Dependency50.P39.amplifierHusimiScaling`). $N\ge1$ (normalization of (1)) and $G>1$ (the paper's $G = e^{(N_1-N_2)\kappa t}>1$; needed for $\beta = \ln(G^2/(G^2-1))$) are added. Realization of the Kraus operators and of $\rho_{\mathrm{in}}$, trace-norm convergence, the density property of $\rho_{\mathrm{out}}$ and summability of each entry of (17) are conclusions, not hypotheses.
-- source:
--   Agarwal, Chaturvedi, Rai, Amplification of NOON States, arXiv:0912.5134v1, p. 3, (17)

import Mathlib
import Definitions.Def_NoonAmp_Symmetric_Model

open QAlgorithms.Papers.Independent.Dependency50.P39

namespace NoonAmp.Symmetric

theorem amplified_noon_density (N : ℕ) (hN : 1 ≤ N) (G : ℝ) (hG : 1 < G) :
    SymAmpRealized G ∧
    HasBipartiteMatrix (noonDensity N) (noonMatrix N) ∧ IsBipartiteDensity (noonDensity N) ∧
    ∃ Y : BipartiteOperator,
      TraceHasSum (fun l : ℕ × ℕ => bipartiteKrausTerm (symAmpKraus G l) (noonDensity N)) Y ∧
      IsBipartiteDensity Y ∧
      (∀ p q : ℕ × ℕ, Summable (noonOutputTerm G N p q)) ∧
      HasBipartiteMatrix Y (noonOutputMatrix G N) := by sorry

end NoonAmp.Symmetric
