-- Prove2me | Theorems.Thm_MulticlassOmni_Lipschitz_lemma_2_2
-- name    : MulticlassOmni.Lipschitz.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:09:53.080193+00:00
-- url     : https://prove2.me/theorems/b2fb28aa-bbab-4a8c-bcc2-553349449466
-- title:
--   Lemma 2.2 — a concave potential with any supergradient selection induces a proper loss
-- statement:
--   Let $H:\Delta_k\to\mathbb R$ be concave and let $\nabla H:\Delta_k\to\mathbb R^k$ be such that $\nabla H(r)$ is a supergradient of $H$ at every $r\in\Delta_k$: $H(q)\le H(r)+\langle\nabla H(r),q-r\rangle$ for all $q\in\Delta_k$. Then $\ell(r,y)=H(r)+\langle\nabla H(r),e_y-r\rangle$ is a proper loss.
--
--   Differences from the source:
--   - encoding: H : Δ_k → ℝ concave and ∇H : Δ_k → ℝ^k → total H : ℝ^k → ℝ and gradH : ℝ^k → ℝ^k with ConcaveOn ℝ (stdSimplex ℝ (Fin k)) H and the supergradient inequality for r, q ∈ stdSimplex; reason: values off the simplex are unconstrained and unused
--   - encoding: '∇H(r) is a supergradient of H at r' (H defined on Δ_k) → H q ≤ H r + ⟨gradH r, q − r⟩ for all q ∈ Δ_k; reason: the supergradient inequality relative to the domain Δ_k of H
--   - encoding: a loss ℓ : Δ_k × [k] → ℝ and properness E_{y∼q}ℓ(q,y) ≤ E_{y∼q}ℓ(r,y) → a total ℓ : ℝ^k → Fin k → ℝ constrained only on stdSimplex; properness is the published UCalibDirichlet.IsProperLoss of its EReal embedding, extended by 0 off the simplex; reason: values off the simplex are never read; for real values the predicate's 'never −∞' clause is automatic, so the instances are the same
--   - encoding: labels [k] = {1, …, k} → Fin k, the source label y is the index y − 1 (label 1 is index 0); reason: relabeling; same instances
-- source:
--   Hu, Luo, Schneider, Yang (2026), Sample Complexity of Multiclass Omniprediction, supplied PDF (SHA-256 aaa73474…584f0, citation basis published; STOC 2027 submission), Lemma 2.2, p. 11

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_ProperLosses

namespace MulticlassOmni.Lipschitz

/-- **Lemma 2.2**, Hu, Luo, Schneider, Yang (2026), p. 11.
Let `H : Δ_k → ℝ` be concave and let `∇H : Δ_k → ℝ^k` be such that `∇H(r)` is a supergradient
of `H` at every `r ∈ Δ_k`, i.e. `H(q) ≤ H(r) + ⟨∇H(r), q - r⟩` for all `q ∈ Δ_k`. Then
`ℓ(r, y) := H(r) + ⟨∇H(r), e_y - r⟩` is a proper loss. -/
theorem lemma_2_2 {k : ℕ} (H : (Fin k → ℝ) → ℝ) (gradH : (Fin k → ℝ) → Fin k → ℝ)
    (hH : ConcaveOn ℝ (stdSimplex ℝ (Fin k)) H)
    (hgrad : ∀ r ∈ stdSimplex ℝ (Fin k), ∀ q ∈ stdSimplex ℝ (Fin k),
      H q ≤ H r + dot (gradH r) (q - r)) :
    IsProper (fun r y => H r + dot (gradH r) (unitVec y - r)) := by sorry

end MulticlassOmni.Lipschitz
