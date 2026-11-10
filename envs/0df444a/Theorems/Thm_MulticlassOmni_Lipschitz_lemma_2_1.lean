-- Prove2me | Theorems.Thm_MulticlassOmni_Lipschitz_lemma_2_1
-- name    : MulticlassOmni.Lipschitz.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:09:42.061197+00:00
-- url     : https://prove2.me/theorems/c01695d8-6ea4-4c65-aa6b-42d4d3e8977d
-- title:
--   Lemma 2.1 (Revelation Principle) — the cost of an argmin action is a proper loss
-- statement:
--   Let $A$ be a set of actions, each $a\in A$ with a cost vector $c_a\in\mathbb R^k$, and let $a(\cdot)$ be a selection with $a(r)\in\arg\min_{a\in A}\langle c_a,r\rangle$ for every $r\in\Delta_k$. Then the loss $\ell(r,y)=(c_{a(r)})_y$ is proper: $\mathbb E_{y\sim q}[\ell(q,y)]\le\mathbb E_{y\sim q}[\ell(r,y)]$ for all $q,r\in\Delta_k$.
--
--   Differences from the source:
--   - generalization: A a non-empty, finite set of actions → A an arbitrary type, with the argmin selection a given as a hypothesis; reason: finiteness and non-emptiness only guarantee that the argmin exists; every source instance supplies such a selection
--   - encoding: a(r) ∈ argmin_{a∈A} ⟨c_a, r⟩ for r ∈ Δ_k → a : ℝ^k → A with ⟨c_{a(r)}, r⟩ ≤ ⟨c_{a'}, r⟩ for all a' and all r ∈ stdSimplex; reason: values of a off the simplex are unconstrained and unused
--   - encoding: a loss ℓ : Δ_k × [k] → ℝ and properness E_{y∼q}ℓ(q,y) ≤ E_{y∼q}ℓ(r,y) → a total ℓ : ℝ^k → Fin k → ℝ constrained only on stdSimplex; properness is the published UCalibDirichlet.IsProperLoss of its EReal embedding, extended by 0 off the simplex; reason: values off the simplex are never read; for real values the predicate's 'never −∞' clause is automatic, so the instances are the same
--   - encoding: labels [k] = {1, …, k} → Fin k, the source label y is the index y − 1 (label 1 is index 0); reason: relabeling; same instances
-- source:
--   Hu, Luo, Schneider, Yang (2026), Sample Complexity of Multiclass Omniprediction, supplied PDF (SHA-256 aaa73474…584f0, citation basis published; STOC 2027 submission), Lemma 2.1, p. 11

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_ProperLosses

namespace MulticlassOmni.Lipschitz

/-- **Lemma 2.1 (Revelation Principle)**, Hu, Luo, Schneider, Yang (2026), p. 11.
Let `A` be a set of actions with cost vectors `c_a ∈ ℝ^k`, and let `a(r)` be a selection with
`a(r) ∈ argmin_{a ∈ A} ⟨c_a, r⟩` for every `r ∈ Δ_k`. Then `ℓ(r, y) := (c_{a(r)})_y` is a proper
loss. -/
theorem lemma_2_1 {k : ℕ} {A : Type*} (c : A → Fin k → ℝ) (a : (Fin k → ℝ) → A)
    (ha : ∀ r ∈ stdSimplex ℝ (Fin k), ∀ a' : A, dot (c (a r)) r ≤ dot (c a') r) :
    IsProper (fun r y => c (a r) y) := by sorry

end MulticlassOmni.Lipschitz
