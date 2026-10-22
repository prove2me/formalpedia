-- Prove2me | Theorems.Thm_NoonAmp_Symmetric_eq_8_16
-- name    : NoonAmp.Symmetric.eq_8_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:36.67647+00:00
-- url     : https://prove2.me/theorems/60409a21-0afc-4e77-9ab3-3a78fd622b39
-- title:
--   (8)+(16), pp. 2–3 — the symmetrically amplified two-mode vacuum is $\rho_G=G^{-4}\sum_{n,m}((G^2-1)/G^2)^{n+m}|n,m\rangle\langle n,m|$
-- statement:
--   Let $G>1$ and let $A_\ell(G)$ be the Kraus operators of the quantum-limited amplifier of amplitude gain $G$. Then every $A_\ell(G)\otimes A_{\ell'}(G)$ is a bounded operator with the product matrix, and the symmetric two-mode amplifier maps the vacuum $\rho_0 = |0,0\rangle\langle0,0|$ to
--   $$\rho_G = \frac1{G^4}e^{-\beta(a^\dagger a+b^\dagger b)},\qquad \beta = \ln\frac{G^2}{G^2-1}:$$
--   the series $\sum_{\ell,\ell'}(A_\ell\otimes A_{\ell'})\rho_0(A_\ell\otimes A_{\ell'})^\dagger$ converges in trace norm to a density operator whose matrix is that of $\rho_G$. Moreover, in the number basis,
--   $$\rho_G = \frac1{G^4}\sum_{n,m=0}^\infty\Big(\frac{G^2-1}{G^2}\Big)^{n+m}|n,m\rangle\langle n,m| .$$
--
--   This is the two-mode form of (8) (the amplified vacuum is thermal with mean photon number $G^2-1$ per mode) together with its number-basis expansion (16); the paper's output state (14) is built on $\rho_G$.
--
--   **Formalization Note** $G>1$ is added; it makes $\beta$ finite and $(G^2-1)/G^2\in(0,1)$. The single-mode form of (8) is part of the open platform theorem `Dependency50.P39.amplifierInputExamples` and is not posed again here. The channel is the Kraus-form quantum-limited amplifier, whose Q action is (7) (`Dependency50.P39.amplifierHusimiScaling`).
-- source:
--   Agarwal, Chaturvedi, Rai, Amplification of NOON States, arXiv:0912.5134v1, p. 2, (8); p. 3, (14), (16)

import Mathlib
import Definitions.Def_NoonAmp_Symmetric_Model

open QAlgorithms.Papers.Independent.Dependency50.P39

namespace NoonAmp.Symmetric

theorem eq_8_16 (G : ℝ) (hG : 1 < G) :
    SymAmpRealized G ∧
    (∃ Y : BipartiteOperator,
      TraceHasSum (fun l : ℕ × ℕ => bipartiteKrausTerm (symAmpKraus G l) vacuumPair) Y ∧
      IsBipartiteDensity Y ∧ HasBipartiteMatrix Y (rhoGMatrix G)) ∧
    ∀ p q : ℕ × ℕ, rhoGMatrix G p q =
      if p = q then (((G ^ 4)⁻¹ * ((G ^ 2 - 1) / G ^ 2) ^ (p.1 + p.2) : ℝ) : ℂ) else 0 := by sorry

end NoonAmp.Symmetric
