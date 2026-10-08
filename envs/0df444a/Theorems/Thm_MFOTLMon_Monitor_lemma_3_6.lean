-- Prove2me | Theorems.Thm_MFOTLMon_Monitor_lemma_3_6
-- name    : MFOTLMon.Monitor.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:52.098982+00:00
-- url     : https://prove2.me/theorems/6c09e8f9-6100-4eed-b01f-a3fe8b11fbd7
-- title:
--   Lemma 3.6, p. 15:11 — next operator: if the p_φ^{D̂_{i+1}}, φ ∈ tsub(β), are regular and correct, p_α^{D̂ᵢ} is regular and equals α^(D̄,τ̄,i)
-- statement:
--   Let $\alpha=\circ_I\beta$ and let $p_\alpha^{\hat{\mathcal D}_i}$ be given by the construction of §3.4.2 from $\hat\beta^{\hat{\mathcal D}_{i+1}}$. If the relations $p_\varphi^{\hat{\mathcal D}_{i+1}}$ are regular and $p_\varphi^{\hat{\mathcal D}_{i+1}}=\varphi^{(\bar{\mathcal D},\bar\tau,i+1)}$ for all $\varphi\in\mathit{tsub}(\beta)$, then
--   $$p_\alpha^{\hat{\mathcal D}_i}\text{ is regular and } p_\alpha^{\hat{\mathcal D}_i}=\alpha^{(\bar{\mathcal D},\bar\tau,i)}.$$
--
--   This is the correctness of the monitor's construction for the next operator.
--
--   **Formalization Note.** As in Lemma 3.5, the auxiliary relations are a family $P(\varphi,j)$ and the structures are automatic with respect to the fixed representation.
-- source:
--   Basin, Klaedtke, Müller, Zălinescu, Monitoring metric first-order temporal properties, J. ACM 62(2), Article 15 (2015), p. 15:11, Lemma 3.6 (construction of §3.4.2)

import Mathlib
import Definitions.Def_MFOTLMon_Monitor_Constructions

namespace MFOTLMon.Monitor

/-- Lemma 3.6 (p. 15:11), `α = ○_I β`. If the relations `p_φ^{D̂_{i+1}}` (here `P φ (i + 1)`) are
regular and equal `φ^{(D̄,τ̄,i+1)}` for all `φ ∈ tsub(β)`, then `p_α^{D̂ᵢ}` is regular and
`p_α^{D̂ᵢ} = α^{(D̄,τ̄,i)}`. Here `p_α^{D̂ᵢ} = nextP τ I i (β̂^{D̂_{i+1}})` (§3.4.2). -/
theorem lemma_3_6 {S : Signature} {Γ : Type} [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S)
    (hD : IsAutomatic rep D) (I : Interval) (β : Formula S)
    (P : Formula S → ℕ → Set (List ℕ)) (i : ℕ) :
    let B : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) β
    (∀ φ ∈ tsub β, RegularRel rep (freeList φ).length (P φ (i + 1)) ∧
      P φ (i + 1) = satSet D φ (i + 1)) →
    RegularRel rep (freeList (Formula.next I β)).length (nextP D.τ I i (B (i + 1))) ∧
      nextP D.τ I i (B (i + 1)) = satSet D (Formula.next I β) i := by sorry

end MFOTLMon.Monitor
