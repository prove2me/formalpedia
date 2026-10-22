-- Prove2me | Theorems.Thm_NoonAmp_Symmetric_eq_14_15
-- name    : NoonAmp.Symmetric.eq_14_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:37.351716+00:00
-- url     : https://prove2.me/theorems/9983307b-9297-49f7-bad1-427116e2321f
-- title:
--   (14)/(15), p. 3 — ρout = (1/(2N!G²ᴺ)) {a†ᴺ + b†ᴺ} ρG {aᴺ + bᴺ}: the amplified NOON state is a two-mode photon-added thermal state
-- statement:
--   Let $N\ge1$, $G>1$, let $\rho_{\mathrm{in}}$ be the NOON density of (11) and $\rho_G$ the amplified two-mode vacuum of (14). Then every $A_\ell(G)\otimes A_{\ell'}(G)$ is a bounded operator with the product matrix, $\rho_{\mathrm{in}}$ is realized, and the series $\sum_{\ell,\ell'}(A_\ell\otimes A_{\ell'})\rho_{\mathrm{in}}(A_\ell\otimes A_{\ell'})^\dagger$ converges in trace norm to a density operator $\rho_{\mathrm{out}}$ with
--   $$\rho_{\mathrm{out}} = \frac{1}{2N!G^{2N}}\big[a^{\dagger N}\rho_Ga^N + a^{\dagger N}\rho_Gb^N + b^{\dagger N}\rho_Ga^N + b^{\dagger N}\rho_Gb^N\big] \tag{14}$$
--   as number-basis matrices. Equivalently,
--   $$\rho_{\mathrm{out}} = \frac{1}{2N!G^{2N}}\{a^{\dagger N}+b^{\dagger N}\}\,\rho_G\,\{a^N+b^N\}. \tag{15}$$
--
--   The output is thus a two-mode photon-added thermal state in which either mode carries the $N$ added photons; the number-basis form (17) follows by expanding the creation and annihilation operators on the diagonal $\rho_G$.
--
--   **Formalization Note** $a^{\dagger N}K$ and $Ka^N$ are index shifts of the matrix $K$ with factor $\sqrt{r!/(r-N)!}$ (see the definitions module); (15) is stated as an identity of such matrices. $N\ge1$ and $G>1$ are added. The channel is the Kraus-form quantum-limited amplifier, whose Q action is (7) (`Dependency50.P39.amplifierHusimiScaling`). Realization, trace-norm convergence and the density property are conclusions.
-- source:
--   Agarwal, Chaturvedi, Rai, Amplification of NOON States, arXiv:0912.5134v1, p. 3, (14), (15)

import Mathlib
import Definitions.Def_NoonAmp_Symmetric_Model

open QAlgorithms.Papers.Independent.Dependency50.P39

namespace NoonAmp.Symmetric

theorem eq_14_15 (N : ℕ) (hN : 1 ≤ N) (G : ℝ) (hG : 1 < G) :
    SymAmpRealized G ∧ HasBipartiteMatrix (noonDensity N) (noonMatrix N) ∧
    (∃ Y : BipartiteOperator,
      TraceHasSum (fun l : ℕ × ℕ => bipartiteKrausTerm (symAmpKraus G l) (noonDensity N)) Y ∧
      IsBipartiteDensity Y ∧ HasBipartiteMatrix Y (photonAddedMatrix G N)) ∧
    ∀ p q : ℕ × ℕ, photonAddedMatrix G N p q =
      (((2 * (N.factorial : ℝ) * G ^ (2 * N))⁻¹ : ℝ) : ℂ) *
        (lowerA N (fun p' q' => raiseA N (rhoGMatrix G) p' q' + raiseB N (rhoGMatrix G) p' q') p q +
          lowerB N (fun p' q' => raiseA N (rhoGMatrix G) p' q' + raiseB N (rhoGMatrix G) p' q') p q) := by sorry

end NoonAmp.Symmetric
