-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_Supplement_lemma_4_1
-- name    : HamSimTradeoff.AncillaDepth.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:52:00.922199+00:00
-- url     : https://prove2.me/theorems/8eefb41f-e02a-48bc-97df-89a43c469841
-- title:
--   Lemma 4.1 — refinement expansion of S₂(t/q)^q in powers of q^{−2} with q-independent coefficients ∥E_ℓ(t)∥ ≤ e²·32^ℓ
-- statement:
--   Let $H_1,\ldots,H_L$ be Hermitian matrices on any positive finite system dimension with $\sum_j\|H_j\|\le1$, put $A=\sum_jH_j$, and let $S_2$ be the symmetric second-order formula (2.1), with weights one. For every real $|t|\le1$ there is one sequence $E_\ell(t)$, independent of the integer refinement $q$, such that for every $q\ge6$,
--   $$S_2(t/q)^q=e^{-itA}+\sum_{\ell=1}^{\infty}q^{-2\ell}E_\ell(t),\qquad \|E_\ell(t)\|\le e^2 32^\ell.$$
--   The series converges in operator norm. This is the uniform refinement expansion used by the multiproduct construction.
--
--   Differences from the source:
--   - encoding: finite complex matrices with spectral norm and one-based indices → Mat n, Fin n, ancilla-first Kronecker products and the L2 operator norm; reason: bijective reindexing; the dimensions, operators and norms are unchanged
--   - encoding: a norm-convergent series indexed by ell >= 1 → HasSum over n >= 0 with ell = n+1; reason: preserves every term and norm convergence, and selects the coefficients before q
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 20, Lemma 4.1

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Hamiltonian
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

theorem lemma_4_1 {L d : ℕ} (hd : 1 ≤ d) (H : Fin L → Mat d)
    (hH : HamiltonianClass H) (t : ℝ) (ht : |t| ≤ 1) :
    ∃ E : ℕ → Mat d,
      (∀ ell : ℕ, 1 ≤ ell → ‖E ell‖ ≤ Real.exp 2 * (32:ℝ)^ell) ∧
      ∀ q : ℕ, 6 ≤ q →
        HasSum (fun n : ℕ => ((q:ℝ)^(-(2*((n+1):ℝ)))) • E (n+1))
          (secondOrder (fun _ => 1) H (t/q)^q - evolution (∑ j, H j) t) := by sorry

end
end HamSimTradeoff.AncillaDepth.Supplement
