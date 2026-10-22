-- Prove2me | Theorems.Thm_OgataLDP_FCS_theorem_1_2
-- name    : OgataLDP.FCS.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:48.082721+00:00
-- url     : https://prove2.me/theorems/191acf06-2939-4dbc-84bc-2f7060b94de9
-- title:
--   Theorem 1.2 — full large-deviation principle with a good rate function for finitely correlated states
-- statement:
--   Let $\omega$ be any $C^*$-finitely correlated state on a one-dimensional quantum spin chain, and let $\Phi$ be any translation-invariant finite-range interaction. For $n\ge1$, let $\mu_{n,\Phi}$ be the spectral distribution, in $\omega$, of $H_\Phi([1,n])/n$. Then there is a good rate function $I:\mathbb R\to[0,\infty]$ for which the sequence $\mu_{n,\Phi}$ satisfies the full large-deviation principle:
--
--   $$\limsup_{n\to\infty}\frac1n\log\mu_{n,\Phi}(C)\le-\inf_{x\in C}I(x)
--     \quad\text{for every closed }C\subseteq\mathbb R,$$
--
--   $$\liminf_{n\to\infty}\frac1n\log\mu_{n,\Phi}(O)\ge-\inf_{x\in O}I(x)
--     \quad\text{for every open }O\subseteq\mathbb R.$$
--
--   This is the paper's main result for finitely correlated states. No ergodicity or spectral-gap hypothesis is imposed on $\omega$.
--
--   **Formalization Note** The local restrictions $\omega_n$ determine each spectral law, so an infinite-chain algebra is not constructed. The rate is existential and can be nonconvex. The printed reduction in Lemma 4.1 omits a mixture step for non-ergodic states; the theorem is posed as printed.
-- source:
--   Ogata, arXiv:0803.0113v1, p. 4, Theorem 1.2; LDP definition on p. 3

import Mathlib
import Definitions.Def_OgataLDP_FCS_Model

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace OgataLDP.FCS

/-- Ogata, arXiv:0803.0113v1, p. 4, Theorem 1.2. -/
theorem theorem_1_2 {σ : Type*} [Fintype σ] [DecidableEq σ] [Nonempty σ] {k : ℕ}
    (F : FCSData σ k) (hF : F.IsValid) (Phi : Interaction σ) :
    ∃ I : ℝ → ℝ≥0∞, IsGoodRate I ∧
      SatisfiesLDP
        (fun n => specDist (F.localState n) (((n : ℝ)⁻¹ : ℝ) • Phi.hamiltonian n)) I := by sorry

end OgataLDP.FCS
