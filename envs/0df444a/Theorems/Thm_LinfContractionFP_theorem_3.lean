-- Prove2me | Theorems.Thm_LinfContractionFP_theorem_3
-- name    : LinfContractionFP.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:17:36.156047+00:00
-- url     : https://prove2.me/theorems/79d093a1-1bfa-466a-bf52-ebdfdb110d57
-- title:
--   Theorem 3 — Amplify terminates and satisfies Contract 1
-- statement:
--   Let $O$ be an Oracle of the extremal amplification game for a secret $\sigma$ at accuracy $\rho>0$. For any shift $b$, margin $\tau>0$, votes $F$ and budgets $B_+,B_->0$, the procedure $\mathrm{Amplify}(b,\tau,F,B_+,B_-)$ terminates and returns either an admission of defeat from Oracle (a defeat that $O$ returned on some call), or a labeling satisfying Contract 1:
--   $$\Phi_+(F)\le B_+\Rightarrow\ell_i=+1\ \forall i\in R_+,\qquad\Phi_-(F)\le B_-\Rightarrow\ell_i=-1\ \forall i\in R_-.$$
--
--   Differences from the source:
--   - encoding: terminates → amplifyRun is a total function whose loop runs its exact iteration count and whose depth bound is never reached; reason: termination is part of the definition
--   - reading: an adversarial Oracle → any adaptive Oracle O : call index → shift → defeat ⊕ labeling whose every labeling meets Problem 1's validity condition; reason: against the deterministic Amplify a history-dependent Oracle is determined by the index of the call, so this covers every adaptive and every stateless Oracle
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Theorem 3, p.16

import Mathlib
import Definitions.Def_LinfContractionFP_IsOracle
import Definitions.Def_LinfContractionFP_Contract1
import Definitions.Def_LinfContractionFP_amplify

namespace LinfContractionFP

/-- Theorem 3: for any shift `b`, margin `τ > 0`, votes `F` and positive budgets `B₊, B₋`,
`Amplify(b, τ, F, B₊, B₋)` terminates and returns either an admission of defeat from Oracle or a
labeling satisfying Contract 1.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), Theorem 3, p.16: "Theorem 3. For any shift b, margin τ > 0, votes F, and positive budgets
B+, B−, the procedure Amplify(b, τ, F, B+, B−) terminates and returns either an admission of
defeat from Oracle, or a labeling satisfying Contract 1."

**Formalization Note.** "Terminates" is carried by `amplifyRun` being a total function whose
loop is the printed loop with its exact iteration count and whose recursion depth bound is never
reached (see `amplifyAux`). An "admission of defeat from Oracle" is a payload `a` that `O`
returned as a defeat on some call. `O` is any Oracle of the game for the secret `σ` at accuracy
`ρ > 0` (`IsOracle`), adaptive: its answer may depend on the index of the call. -/
theorem theorem_3 {κ α : Type} [Fintype κ] (σ : κ → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (O : ℕ → (κ → ℝ) → α ⊕ (κ → Lbl)) (hO : IsOracle σ ρ O) (b : κ → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (F : κ → ℤ) (Bp Bm : ℝ) (hBp : 0 < Bp) (hBm : 0 < Bm) :
    (∀ a, (amplifyRun O ρ b τ F Bp Bm).1 = Sum.inl a → ∃ t b', O t b' = Sum.inl a) ∧
      (∀ ℓ, (amplifyRun O ρ b τ F Bp Bm).1 = Sum.inr ℓ → Contract1 σ b τ F Bp Bm ℓ) := by sorry

end LinfContractionFP
