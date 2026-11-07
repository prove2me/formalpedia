-- Prove2me | Theorems.Thm_FreeSpencer_lemma_C_2
-- name    : FreeSpencer.lemma_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:31.928999+00:00
-- url     : https://prove2.me/theorems/d0f37051-801d-4499-8fa6-a91036e2cf1f
-- title:
--   Lemma C.2, pp.79–80 — preparation moves
-- statement:
--   For the mode of $n\ge32$, $m\ge1$, epoch size $1\le\ell\le n$, and centers with $\|H\|_{op}\le n+1$: every step of Prepare, a cleanup or a cut, leaves $H$ fixed and decreases $C$ in positive semidefinite order. A return gives either zero covariance or a covariance with positive eigenvalues at least $2\delta$ and
--   $$\Gamma|_{\mathrm{ran}\,C}\preceq t_\ell I.$$
--   Each cut lowers the potential by at least $t_\ell\alpha_\ell/2$. Across an entire epoch trial there are at most $\lfloor\ell/\alpha_\ell\rfloor$ cuts, and the total cleanup loss is at most $2\delta\ell=\ell/4096\le\ell/1024$. Every call terminates: at each covariance a return or a further step is available, and no infinite chain of steps exists.
--
--   Differences from the source:
--   - generalization: the procedure Prepare with exact eigendecompositions → every run in the form of App. F.2: any cleanup step of Lemma F.2 type, any estimate with error ≤ t_ℓ/64, any unit v over the spike threshold; reason: App. F: "The proof of Lemma C.2 uses only these two facts"; the eigendecomposition form is one instance
--   - generalization: the center H(x) of a point of the cube, ‖H‖ ≤ n → any symmetric H with ‖H‖ ≤ n + 1; reason: this is the range of Theorem D.1, on which the proof relies
--   - encoding: "every call terminates" → a progress clause and Acc of the step relation; reason: every chain of steps is finite, and only a return has no next step
--   - encoding: C on ℝ^{I₀}, starting at I_ℓ → C on ℝⁿ, starting at the diagonal projection on I₀; reason: Remark 7.2 (p.49): all n coordinates may be kept; the zero rows do not change η_C
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma C.2, pp.79–80; Appendix F.2, p.89

import Mathlib
import Definitions.Def_FreeSpencer_PrepStep
import Definitions.Def_FreeSpencer_trialLaw
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- **Lemma C.2** (Preparation moves and the termination of preparation), over every run of Prepare in
the form of Appendix F. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma C.2, pp.79–80; Appendix F.2, p.89 ("The proof of
Lemma C.2 uses only these two facts").

**Formalization Note** Prepare is a relation: `PrepStep` is any cleanup step or any cut on any estimate
`Ĝ` with `‖Ĝ - Γ‖_{op, ran C} ≤ t_ℓ/64`, and `PrepDone` is a return; the exact eigendecomposition form
is one instance. "Every call terminates" is `Acc` of the step relation with the progress clause. "Across
an entire epoch trial" is `EpochRun`. The center satisfies `‖H‖ ≤ n + 1`, the range of Theorem D.1; the
walk has `‖H‖ ≤ n`. The mode is the one of p.77, with `n ≥ 32`, `m ≥ 1`. -/
theorem lemma_C_2 {n m ℓ : ℕ} (hn : 32 ≤ n) (hm : 1 ≤ m) (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n)
    (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (hsymm : ∀ i, (A i).IsSymm) (hA : ∀ i, ‖A i‖ ≤ 1) :
    let par := params n m
    (∀ (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) (C C' : Matrix (Fin n) (Fin n) ℝ), H.IsSymm →
      ‖H‖ ≤ (n : ℝ) + 1 → C.PosSemidef → (1 - C).PosSemidef → PrepStep A par ℓ H C C' →
      C'.PosSemidef ∧ (C - C').PosSemidef) ∧
    (∀ (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) (C : Matrix (Fin n) (Fin n) ℝ), H.IsSymm →
      ‖H‖ ≤ (n : ℝ) + 1 → C.PosSemidef → (1 - C).PosSemidef → PrepDone A par ℓ H C →
      C = 0 ∨ (CovFloor C ∧ NoSpike par.q par.θ par.κ (liftFam A) H C (tEll ℓ))) ∧
    (∀ (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) (C C' : Matrix (Fin n) (Fin n) ℝ), H.IsSymm →
      ‖H‖ ≤ (n : ℝ) + 1 → C.PosSemidef → (1 - C).PosSemidef → CutStep A par ℓ H C C' →
      tEll ℓ * alphaEll n m ℓ / 2 ≤ Epot par A H C - Epot par A H C') ∧
    (∀ (I₀ : Finset (Fin n)) (C : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (u : ℝ), I₀.card = ℓ →
      EpochRun A par ℓ (diagOn I₀) C k u →
      k ≤ ⌊(ℓ : ℝ) / alphaEll n m ℓ⌋₊ ∧ u ≤ 2 * deltaC * ℓ) ∧
    2 * deltaC * ℓ = (ℓ : ℝ) / 4096 ∧ (ℓ : ℝ) / 4096 ≤ (ℓ : ℝ) / 1024 ∧
    (∀ (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) (C : Matrix (Fin n) (Fin n) ℝ), H.IsSymm →
      ‖H‖ ≤ (n : ℝ) + 1 → C.PosSemidef → (1 - C).PosSemidef →
      (PrepDone A par ℓ H C ∨ ∃ C', PrepStep A par ℓ H C C') ∧
      Acc (fun C₂ C₁ => PrepStep A par ℓ H C₁ C₂) C) := by sorry

end FreeSpencer
