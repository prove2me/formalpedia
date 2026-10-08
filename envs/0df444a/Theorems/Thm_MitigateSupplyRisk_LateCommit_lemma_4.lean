-- Prove2me | Theorems.Thm_MitigateSupplyRisk_LateCommit_lemma_4
-- name    : MitigateSupplyRisk.LateCommit.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:28.485983+00:00
-- url     : https://prove2.me/theorems/b15d44c9-3278-4176-8fe3-ff045458b459
-- title:
--   Lemma 4, p. 498 — a_i^{*L} ≤ a_i^{*E}: late commitment targets a weakly lower reliability index
-- statement:
--   Let $(a_1^L,a_2^L)$ maximize the late-commitment profit $\Pi_1^L$ of (9) over $a_1\ge a_1^0$, $a_2\ge a_2^0$. For $i=1,2$ let $a_i^E\ge a_i^0$ maximize supplier $i$'s early-commitment profit $\Pi_{1i}^E$ of (7) over $a\ge a_i^0$. Then for each $i$
--   $$\max\{a_i^L,a_i^E\}\ \text{also maximizes}\ \Pi_{1i}^E\ \text{over}\ a\ge a_i^0 .$$
--   In particular, some optimal early-commitment index of supplier $i$ is at least $a_i^L$. When $\Pi_{1i}^E$ has a unique maximizer $a_i^{*E}$, this is the paper's $a_i^{*L}\le a_i^{*E}$.
--
--   Late commitment therefore asks for a (weakly) lower reliability target, that is, less improvement effort, than early commitment: in late commitment the improved supplier is used only if it turns out to be preferred.
--
--   **Formalization Note** The paper writes $a_i^{*L}\le a_i^{*E}$ as if optimizers were unique. $\Pi_1^L$ is "neither concave nor unimodal" (p. 498), and $\Pi_{1i}^E$ need not have a unique maximizer, so the comparison is stated for arbitrary maximizers in the form above, which reduces to the printed inequality when the early optimizer is unique. The existence of maximizers is a hypothesis, not a claim.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 498 (PDF p. 10), Lemma 4

import Mathlib
import Definitions.Def_MitigateSupplyRisk_LateCommit_Model

namespace MitigateSupplyRisk.LateCommit

/-- Lemma 4 (p. 498), `a_i^{*L} ≤ a_i^{*E}`, in the form valid for non-unique optimizers: if
`(a₁ᴸ, a₂ᴸ)` maximizes the late-commitment profit (9) over `a₁ ≥ a₁⁰, a₂ ≥ a₂⁰` and `aᵢᴱ`
maximizes supplier `i`'s early-commitment profit (7) over `aᵢ ≥ aᵢ⁰`, then `max(aᵢᴸ, aᵢᴱ)` is
also an early-commitment maximizer for supplier `i`, i.e. some early optimizer is `≥ aᵢᴸ`. -/
theorem lemma_4 (X : Setting) {a₁L a₂L a₁E a₂E : ℝ}
    (hL : (a₁L, a₂L) ∈ X.lateFeasible)
    (hLmax : IsMaxOn (fun a : ℝ × ℝ => X.lateProfit a.1 a.2) X.lateFeasible (a₁L, a₂L))
    (h₁E : X.I₁.a0 ≤ a₁E) (h₁Emax : IsMaxOn X.early₁ (Set.Ici X.I₁.a0) a₁E)
    (h₂E : X.I₂.a0 ≤ a₂E) (h₂Emax : IsMaxOn X.early₂ (Set.Ici X.I₂.a0) a₂E) :
    IsMaxOn X.early₁ (Set.Ici X.I₁.a0) (max a₁L a₁E) ∧
      IsMaxOn X.early₂ (Set.Ici X.I₂.a0) (max a₂L a₂E) := by sorry

end MitigateSupplyRisk.LateCommit
