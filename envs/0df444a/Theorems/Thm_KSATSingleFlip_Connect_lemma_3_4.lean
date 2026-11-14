-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_3_4
-- name    : KSATSingleFlip.Connect.lemma_3_4
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:21:20.8842+00:00
-- url     : https://prove2.me/theorems/c7b5e1d0-2f30-4325-9ce0-42af77d2304c
-- title:
--   Lemma 3.4 — Averaging literal signs
-- statement:
--   Title: Lemma 3.4 — Averaging literal signs
--
--   Let Φ₀ be a finite Boolean formula, and append r clauses with fixed k-variable scopes and independent uniform signs. Choose a designated variable vᵢ in each scope, let S be the assignments for which every appended clause forces its designated variable, and let A be a set of solutions of Φ₀. If B contains all designated variables and τ is a feasible assignment on B, then
--
--   $$\mathbb E_{\mathrm{signs}}\,\mu_\Phi(S\cap A\cap\{\sigma_B=\tau\})\le 2^{-kr}\mu_{\Phi_0}(A\mid\sigma_B=\tau),$$
--
--   and
--
--   $$\mathbb E_{\mathrm{signs}}\,\mu_\Phi(S\cap A)\le 2^{|B|-kr}.$$
--
--   The formalization samples a full sign function for each clause and ignores signs outside that clause's scope; this induces independent uniform signs on every scope. It is an open target.
--
--   Source: Chunyang Wang, Yitong Yin, Yixiao Yu, and Yiyao Zhang, *Single-Variable Connectivity in Random k-SAT*, Lemma 3.4, printed p. 16 (PDF p. 18 of STOC 2027 submission #737), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf.
-- source:
--   Chunyang Wang, Yitong Yin, Yixiao Yu, Yiyao Zhang, Single-Variable Connectivity in Random k-SAT, STOC 2027 submission #737, Lemma 3.4, printed p. 16 (PDF p. 18), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SignAveraging

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- Lemma 3.4: averaging independent literal signs bounds the mass of
assignments at which all resampled clauses force designated variables. -/
theorem lemma_3_4 {n k r : ℕ} (Φ0 : GFormula (Fin n))
    (scopes : Fin r → Finset (Fin n)) (designated : Fin r → Fin n)
    (hscopes : ∀ i, (scopes i).card = k) (hdesignated : ∀ i, designated i ∈ scopes i)
    (A : Finset (Fin n → Bool)) (hA : A ⊆ sols Φ0)
    (B : Finset (Fin n)) (hB : ∀ i, designated i ∈ B) (τ : Fin n → Bool)
    (hτ : ((sols Φ0).filter (agreesOn B τ)).Nonempty) :
    (uexp (fun signs : Fin r → Fin n → Bool =>
      mass (signExtendedFormula Φ0 scopes signs)
        (A.filter fun σ => allResampledClausesForce scopes signs designated σ ∧ agreesOn B τ σ)) ≤
      (1 / (2 : ℝ) ^ (k * r)) * conditionalSolutionMass Φ0 A B τ) ∧
    (uexp (fun signs : Fin r → Fin n → Bool =>
      mass (signExtendedFormula Φ0 scopes signs)
        (A.filter fun σ => allResampledClausesForce scopes signs designated σ)) ≤
      (2 : ℝ) ^ B.card / (2 : ℝ) ^ (k * r)) := by
  sorry

end KSATSingleFlip.Connect
