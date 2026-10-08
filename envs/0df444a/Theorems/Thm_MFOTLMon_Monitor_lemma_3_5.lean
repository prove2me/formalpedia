-- Prove2me | Theorems.Thm_MFOTLMon_Monitor_lemma_3_5
-- name    : MFOTLMon.Monitor.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:40:51.950884+00:00
-- url     : https://prove2.me/theorems/98841e03-02ee-4507-beae-ada25baac00a
-- title:
--   Lemma 3.5, p. 15:10 — previous operator: p_α^{D̂₀} = α^(D̄,τ̄,0) = ∅, and p_α^{D̂ᵢ} is regular and equals α^(D̄,τ̄,i) for i > 0
-- statement:
--   Let $\alpha=\bullet_I\beta$ and let $p_\alpha^{\hat{\mathcal D}_i}$ be given by the construction of §3.4.1 from $\hat\beta^{\hat{\mathcal D}_{i-1}}$, where each $\hat{\mathcal D}_j$ interprets the predicates of $R$ as $\mathcal D_j$ does and each $p_\varphi$ by a relation $p_\varphi^{\hat{\mathcal D}_j}$. Then:
--
--   1. $p_\alpha^{\hat{\mathcal D}_0}$ is regular and $p_\alpha^{\hat{\mathcal D}_0}=\alpha^{(\bar{\mathcal D},\bar\tau,0)}=\emptyset$;
--   2. for $i>0$, if the relations $p_\varphi^{\hat{\mathcal D}_{i-1}}$ are regular and $p_\varphi^{\hat{\mathcal D}_{i-1}}=\varphi^{(\bar{\mathcal D},\bar\tau,i-1)}$ for all $\varphi\in\mathit{tsub}(\beta)$, then
--   $$p_\alpha^{\hat{\mathcal D}_i}\text{ is regular and } p_\alpha^{\hat{\mathcal D}_i}=\alpha^{(\bar{\mathcal D},\bar\tau,i)}.$$
--
--   This is the correctness of the monitor's construction for the previous operator.
--
--   **Formalization Note.** The auxiliary relations are a family $P(\varphi,j)$; $\hat\beta^{\hat{\mathcal D}_j}$ is `hatSet (D.rel j) D.const (P · j) β`. The structures are automatic with respect to the fixed representation (hypothesis `hD`).
-- source:
--   Basin, Klaedtke, Müller, Zălinescu, Monitoring metric first-order temporal properties, J. ACM 62(2), Article 15 (2015), p. 15:10, Lemma 3.5 (construction of §3.4.1)

import Mathlib
import Definitions.Def_MFOTLMon_Monitor_Constructions

namespace MFOTLMon.Monitor

/-- Lemma 3.5 (p. 15:10), `α = ●_I β`. The relation `p_α^{D̂₀}` is regular and
`p_α^{D̂₀} = α^{(D̄,τ̄,0)} = ∅`. For `i > 0`, if the relations `p_φ^{D̂_{i−1}}` (here `P φ (i − 1)`)
are regular and equal `φ^{(D̄,τ̄,i−1)}` for all `φ ∈ tsub(β)`, then `p_α^{D̂ᵢ}` is regular and
`p_α^{D̂ᵢ} = α^{(D̄,τ̄,i)}`. Here `p_α^{D̂ᵢ} = prevP τ I i (β̂^{D̂_{i−1}})` (§3.4.1). -/
theorem lemma_3_5 {S : Signature} {Γ : Type} [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S)
    (hD : IsAutomatic rep D) (I : Interval) (β : Formula S)
    (P : Formula S → ℕ → Set (List ℕ)) :
    let B : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) β
    (RegularRel rep (freeList (Formula.prev I β)).length (prevP D.τ I 0 (B 0)) ∧
      prevP D.τ I 0 (B 0) = satSet D (Formula.prev I β) 0 ∧
      satSet D (Formula.prev I β) 0 = ∅) ∧
    ∀ i, 0 < i →
      (∀ φ ∈ tsub β, RegularRel rep (freeList φ).length (P φ (i - 1)) ∧
        P φ (i - 1) = satSet D φ (i - 1)) →
      RegularRel rep (freeList (Formula.prev I β)).length (prevP D.τ I i (B (i - 1))) ∧
        prevP D.τ I i (B (i - 1)) = satSet D (Formula.prev I β) i := by sorry

end MFOTLMon.Monitor
