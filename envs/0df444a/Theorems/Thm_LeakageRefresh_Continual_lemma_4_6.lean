-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_lemma_4_6
-- name    : LeakageRefresh.Continual.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:11:40.605537+00:00
-- url     : https://prove2.me/theorems/00d93736-812e-4684-abc1-c68653169c08
-- title:
--   Lemma 4.6 — approximation of an answer: $\|\mathrm{prob}_z^{>\beta}\|_*\le2$, $\|\mathrm{prob}_z^{>\beta}\|_2\le1$, $\|\Delta_z\|_2\le C\beta^{1/3}$, energies $\le1/\beta$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $n\ge2$, $q=2^n-1$; fix the leakage functions of a round (a formal incoming history and the adversary's tape), an answer $z$, an orthonormal expansion of $\mathrm{prob}_z$, and a threshold $\beta\in[q^{-1/3},1]$. Then the truncation of Eq. (4.7) and its residual $\Delta_z=\mathrm{prob}_z-2\,\mathrm{project}(\mathrm{prob}_z^{>\beta})$ satisfy
--   $$\|\mathrm{prob}_z^{>\beta}\|_*\le2,\qquad\|\mathrm{prob}_z^{>\beta}\|_2\le1,\qquad\|\Delta_z\|_2\le C\beta^{1/3}, \tag{4.9–4.11}$$
--   and the energies of the balanced factors $\sqrt{\sigma_j}u_j$, $\sqrt{\sigma_j}v_j$ satisfy $\Phi_\beta(\ell,\ell')\le1/\beta$ and $\Psi_\beta(r,r')\le1/\beta$ at every input (4.12–4.13). Both mean energies equal $\|\mathrm{prob}_z^{>\beta}\|_*$ (hence are at most $2$). The same $C$ serves every dimension, threshold, answer, history and pair of leakage functions.
--
--   Differences from the source:
--   - encoding: a fixed formal incoming history and adversary tape (which fix the two leakage functions) → an arbitrary pair of leakage functions `lp : LeakPair n lam`; reason: every pair of leakage functions arises from some strategy, history and tape, and conversely
--   - reading: the truncation $\mathrm{prob}_z^{>\beta}$ of "an orthonormal expansion" of $\mathrm{prob}_z$ (Eq. (4.7)) → the statement holds for every orthonormal expansion `E : OrthoExpansion (probTable lp z)`; reason: the paper takes an arbitrary expansion and notes the truncation does not depend on it; quantifying over all expansions is that reading
--   - encoding: "both mean energies equal $\|\mathrm{prob}_z^{>\beta}\|_*$ by Eq. (2.9), and hence are at most 2" → two conjuncts `avg (E.truncPhi β) = nuclearNorm (E.trunc β)` and the same for `truncPsi`; reason: the bound by 2 follows from these and (4.9)
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 31, Lemma 4.6

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding
import Definitions.Def_LeakageRefresh_Continual_LeakageModel
import Definitions.Def_LeakageRefresh_Continual_Tables
import Definitions.Def_LeakageRefresh_Continual_OneRound

namespace LeakageRefresh.Continual

/-- **Lemma 4.6 (Approximation of an answer under refreshing).** There is an absolute constant
`C > 0` such that for every `n ≥ 2` (`q = 2ⁿ − 1`), all fixed leakage functions `lp` (a fixed
formal incoming history and adversary tape), every answer `z`, every `β ∈ [q^{−1/3}, 1]` and
every orthonormal expansion of `prob_z`: (4.9) `‖prob_z^{>β}‖_* ≤ 2`, (4.10)
`‖prob_z^{>β}‖₂ ≤ 1`, (4.11) `‖∆_z‖₂ ≤ C β^{1/3}`, (4.12)–(4.13) the energies of the balanced
factors satisfy `Φ_β ≤ 1/β` and `Ψ_β ≤ 1/β` at every input, and both mean energies equal
`‖prob_z^{>β}‖_*`. -/
theorem lemma_4_6 :
    ∃ C : ℝ, 0 < C ∧
      ∀ n lam : ℕ, 2 ≤ n →
      ∀ (lp : LeakPair n lam) (z : Answer lam) (β : ℝ),
        ((2 : ℝ) ^ n - 1) ^ (-(1 / 3 : ℝ)) ≤ β → β ≤ 1 →
        ∀ E : OrthoExpansion (probTable lp z),
          nuclearNorm (E.trunc β) ≤ 2 ∧
          tableL2 (E.trunc β) ≤ 1 ∧
          tableL2 (residual E β) ≤ C * β ^ (1 / 3 : ℝ) ∧
          (∀ x, E.truncPhi β x ≤ 1 / β) ∧
          (∀ y, E.truncPsi β y ≤ 1 / β) ∧
          avg (E.truncPhi β) = nuclearNorm (E.trunc β) ∧
          avg (E.truncPsi β) = nuclearNorm (E.trunc β) := by sorry

end LeakageRefresh.Continual
