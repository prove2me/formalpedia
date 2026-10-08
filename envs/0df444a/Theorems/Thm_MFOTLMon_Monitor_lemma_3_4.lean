-- Prove2me | Theorems.Thm_MFOTLMon_Monitor_lemma_3_4
-- name    : MFOTLMon.Monitor.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:42.867542+00:00
-- url     : https://prove2.me/theorems/4eda8b08-4d96-4f2f-8a47-f27cbc4f9fc3
-- title:
--   Lemma 3.4, p. 15:10 — φ̂^{D̂ᵢ} = φ^(D̄,τ̄,i) once the auxiliary relations of tsub(φ) are right, and φ̂^{D̂ᵢ} is regular once they are regular
-- statement:
--   Let $(\bar{\mathcal D},\bar\tau)$ be a temporal structure with domain $\mathbb N$ whose structures are automatic with respect to a fixed constant domain representation, and fix a time point $i$. Let $\hat{\mathcal D}_i$ be an extension of $\mathcal D_i$ to the extended signature: it interprets the predicates of $R$ and the constants as $\mathcal D_i$ does, and each auxiliary predicate $p_\psi$ by a relation $p_\psi^{\hat{\mathcal D}_i}$. Then for every formula $\varphi$:
--
--   1. if $p_\psi^{\hat{\mathcal D}_i}=\psi^{(\bar{\mathcal D},\bar\tau,i)}$ for all $\psi\in\mathit{tsub}(\varphi)$, then
--   $$\hat\varphi^{\hat{\mathcal D}_i}=\varphi^{(\bar{\mathcal D},\bar\tau,i)};$$
--   2. if $p_\psi^{\hat{\mathcal D}_i}$ is regular for all $\psi\in\mathit{tsub}(\varphi)$, then $\hat\varphi^{\hat{\mathcal D}_i}$ is regular.
--
--   The lemma is the bridge between the first-order formula $\hat\Phi$ the monitor evaluates and the temporal semantics of $\Phi$; each of Lemmas 3.5–3.8 applies it to the direct subformulas of a temporal operator.
--
--   **Formalization Note.** The relations $p_\psi^{\hat{\mathcal D}_i}$ are an arbitrary family $P$. The page states the lemma for subformulas of $\Phi$; it is stated here for every formula, which is stronger. Regularity is with respect to the fixed representation `rep`, and the arity of a satisfying set is the number of free variables.
-- source:
--   Basin, Klaedtke, Müller, Zălinescu, Monitoring metric first-order temporal properties, J. ACM 62(2), Article 15 (2015), p. 15:10, Lemma 3.4

import Mathlib
import Definitions.Def_MFOTLMon_Monitor_Constructions

namespace MFOTLMon.Monitor

/-- Lemma 3.4 (p. 15:10). Let the extended structure `D̂ᵢ` interpret `R` and `C` as `Dᵢ` does and the
auxiliary predicate `p_ψ` by `P ψ`. (i) If `P ψ = ψ^{(D̄,τ̄,i)}` for all `ψ ∈ tsub(φ)`, then
`φ̂^{D̂ᵢ} = φ^{(D̄,τ̄,i)}`. (ii) If every `P ψ`, `ψ ∈ tsub(φ)`, is regular, then `φ̂^{D̂ᵢ}` is regular.
Stated for every formula `φ` (the page says every subformula of `Φ`). -/
theorem lemma_3_4 {S : Signature} {Γ : Type} [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S)
    (hD : IsAutomatic rep D) (i : ℕ) (P : Formula S → Set (List ℕ)) (φ : Formula S) :
    ((∀ ψ ∈ tsub φ, P ψ = satSet D ψ i) → hatSet (D.rel i) D.const P φ = satSet D φ i) ∧
    ((∀ ψ ∈ tsub φ, RegularRel rep (freeList ψ).length (P ψ)) →
      RegularRel rep (freeList φ).length (hatSet (D.rel i) D.const P φ)) := by sorry

end MFOTLMon.Monitor
