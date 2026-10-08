-- Prove2me | Theorems.Thm_MFOTLMon_Monitor_relations_built_correct
-- name    : MFOTLMon.Monitor.relations_built_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:38:12.887025+00:00
-- url     : https://prove2.me/theorems/732a101f-613c-47d4-95da-88b2658a2813
-- title:
--   Proof of Theorem 3.9, p. 15:17 — if (α, j, ∅) ∈ Q_k, line 7 builds p_α^{D̂ⱼ} from stored relations, and it equals α^(D̄,τ̄,j) and is regular
-- statement:
--   Assume the hypotheses of Theorem 3.9: the input structures are automatic with respect to a fixed constant domain representation of $\mathbb N$ and interpret a binary $\prec$ as $<$; $\Phi$ is bounded, each temporal subformula occurs once in $\Phi$, and the direct subformulas of every $\mathsf S_I$ and $\mathsf U_I$ subformula have the same free variables. Let $Q_k$ be the list $Q$ of $\mathsf M_\Phi$ on entering its $(k+1)$st loop iteration. If $(\alpha,j,\emptyset)\in Q_k$, then after lines 5–7 of that iteration the store contains $p_\alpha^{\hat{\mathcal D}_j}$, and
--   $$p_\alpha^{\hat{\mathcal D}_j}=\alpha^{(\bar{\mathcal D},\bar\tau,j)}\quad\text{and}\quad\alpha^{(\bar{\mathcal D},\bar\tau,j)}\text{ is regular.}$$
--
--   This is what the paper draws from the claim that line 7 can be executed (every input of the construction has been built earlier and not yet discarded), combined with Lemmas 3.5–3.8; it yields part (i) of Theorem 3.9.
--
--   **Formalization Note.** The store after line 7 is `afterBuild D (run D Φ k)`. A build whose input is absent from the store stores nothing, so the conclusion includes that the build succeeded.
-- source:
--   Basin, Klaedtke, Müller, Zălinescu, Monitoring metric first-order temporal properties, J. ACM 62(2), Article 15 (2015), p. 15:17, proof of Theorem 3.9, claim that line 7 can be executed and its consequence p_α^{D̂j} = α^(D̄,τ̄,j)

import Mathlib
import Definitions.Def_MFOTLMon_Monitor_Algorithm

namespace MFOTLMon.Monitor

/-- The conclusion drawn from "line 7 can be executed" in the proof of Theorem 3.9 (p. 15:17): if
`(α, j, ∅) ∈ Q_k`, then line 7 of the `(k+1)`st iteration builds `p_α^{D̂ⱼ}` from the store, and it
equals `α^{(D̄,τ̄,j)}` and is regular. -/
theorem relations_built_correct {S : Signature} {Γ : Type} [Fintype Γ] (rep : DomainRep Γ)
    (D : TempStruct S) (hD : IsAutomatic rep D) (hlt : HasOrderPred D) (Φ : Formula S)
    (hΦ : Bounded Φ) (huniq : TemporalSubformulasOnce Φ) (hfree : DirectFreeAligned Φ) :
    ∀ (k : ℕ) (α : Formula S) (j : ℕ), (α, j, ([] : List (Formula S))) ∈ (run D Φ k).Q →
      (afterBuild D (run D Φ k)).store (Key.p α) j = some (satSet D α j) ∧
        RegularRel rep (freeList α).length (satSet D α j) := by sorry

end MFOTLMon.Monitor
