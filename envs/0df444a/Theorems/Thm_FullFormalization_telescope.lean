-- Prove2me | Theorems.Thm_FullFormalization_telescope
-- name    : FullFormalization.telescope
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:54:58.540732+00:00
-- url     : https://prove2.me/theorems/285b7c6b-a4c4-44d7-ac1c-932919647de6
-- title:
--   Telescoping the local identities into the master certificate
-- statement:
--   Summing the local certificate decrements along the trajectory collapses the interior potential and yields the master certificate
--   $$\tau\|r\|^2 - F_N = \sum_{j=0}^{N-1} a_j I_{j,j+1} \;+\; \sum_{j=0}^{N} b_j I_{\star,j} \;+\; \sum_{j=0}^{N-1} S_j ,$$
--   where $I_{j,j+1}$ are the interior gradient/function-value terms, $I_{\star,j}$ the residual terms, $S_j$ the nonnegative square terms, and $a_j, b_j$ the interpolation weights. The local inputs are the initial identity $-V_1 = a_0(I_{\star,0}+I_{0,1}) + S_0$, the interior/terminal decrements $V_{j+1}-V_j = -(b_j I_{\star,j} + a_j I_{j,j+1} + S_j)$ for $1 \le j \le N-1$, the endpoint identity $\tau\|r\|^2 - F_N = -V_N + b_N I_{\star,N}$, and $b_0 = a_0$. This is the master certificate (7.1) of source §12.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §12, eq. (7.1) and (12.1)-(12.3); Lean: FullFormalization.MasterCertificate lines 29-81

-- Generated from F:/20261008/FullFormalization\FullFormalization\MasterCertificate.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.MasterCertificate

  Source section 12: the telescoping step that turns the four *local*
  certificate identities into the master certificate (7.1)

      τ‖r‖² - F_N = Σ_{j=0}^{N-1} a_j I_{j,j+1} + Σ_{j=0}^{N} b_j I_{⋆,j}
                    + Σ_{j=0}^{N-1} S_j.

  This file isolates the pure summation content.  The local identities enter
  as hypotheses:

    * `hinit`  — (9.1), rewritten as `-V_1 = a_0(I_{⋆,0} + I_{0,1}) + S_0`;
    * `hstep`  — (10.1) for `1 ≤ j ≤ N-2` together with (11.1) at `j = N-1`;
    * `hend`   — (11.2);
    * `hb0`    — `b_0 = a_0` (source line 1329: `b_0 = a_0 - a_{-1} = a_0`,
                 using `a_{-1} = 0` from (4.12)).

  Once the concrete local identities land, (7.1) is `telescope` applied to
  them — see `FORMALIZATION_STATUS.md`.
-/

import Mathlib

set_option linter.unusedSectionVars false

namespace FullFormalization



end FullFormalization

open FullFormalization

set_option linter.unusedSectionVars false

theorem FullFormalization.telescope {N : ℕ} (hN : 2 ≤ N)
    (V : ℕ → ℝ) (a b Ii Is S : ℕ → ℝ) (tauR2 FN : ℝ)
    (hb0 : b 0 = a 0)
    (hinit : V 1 = -(a 0 * (Is 0 + Ii 0) + S 0))
    (hstep : ∀ j, 1 ≤ j → j ≤ N - 1 →
      V (j + 1) - V j = -(b j * Is j + a j * Ii j + S j))
    (hend : tauR2 - FN = -V N + b N * Is N) :
    tauR2 - FN = (∑ j ∈ Finset.range N, a j * Ii j)
      + (∑ j ∈ Finset.range (N + 1), b j * Is j)
      + (∑ j ∈ Finset.range N, S j) := by sorry
