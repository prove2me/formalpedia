-- Prove2me | Theorems.Thm_OgataLDP_FCS_claim_15
-- name    : OgataLDP.FCS.claim_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:39.129297+00:00
-- url     : https://prove2.me/theorems/b82ca8df-1dae-488c-913b-919509cb7d51
-- title:
--   Claim (15) — a spectral gap for the auxiliary transfer map gives a two-sided order bound
-- statement:
--   Let $(\mathcal B,\mathcal E,\rho)$ generate a finitely correlated state, and write $\widehat{\mathcal E}_1(b)=\mathcal E(1\otimes b)$. Suppose the eigenvalue $1$ is algebraically simple and every other eigenvalue has modulus strictly below $1$. Then there are an integer $l$ and $s>0$ such that every positive $b\in\mathcal B$ satisfies
--
--   $$s^{-1}\rho(b)\,1\ \le\ (\widehat{\mathcal E}_1)^{l}(b)\ \le\ s\rho(b)\,1.$$
--
--   This is the order estimate used to pass to a blocked auxiliary transfer map satisfying condition (14).
--
--   **Formalization Note** Algebraic simplicity means that the maximal generalized eigenspace at $1$ is the span of the identity. The inequalities use the Loewner order.
-- source:
--   Ogata, arXiv:0803.0113v1, p. 12, claim (15) in the proof of Lemma 4.1

import Mathlib
import Definitions.Def_OgataLDP_FCS_Model

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder MatrixOrder

namespace OgataLDP.FCS

/-- Ogata, arXiv:0803.0113v1, p. 12, claim (15) in Lemma 4.1's proof. -/
theorem claim_15 {σ : Type*} [Fintype σ] [DecidableEq σ] [Nonempty σ] {k : ℕ}
    (F : FCSData σ k) (hF : F.IsValid)
    (hspectrum : ∀ z : ℂ, F.Ehat1.HasEigenvalue z → z = 1 ∨ ‖z‖ < 1)
    (hsimple : F.Ehat1.maxGenEigenspace 1 =
      Submodule.span ℂ {(1 : Matrix (Fin k) (Fin k) ℂ)}) :
    ∃ (l : ℕ) (s : ℝ), 0 < s ∧
      ∀ b : Matrix (Fin k) (Fin k) ℂ, b.PosSemidef →
        ((s⁻¹ * F.rhoState b : ℝ) : ℂ) • 1 ≤ (F.Ehat1 ^ l) b ∧
        (F.Ehat1 ^ l) b ≤ ((s * F.rhoState b : ℝ) : ℂ) • 1 := by sorry

end OgataLDP.FCS
