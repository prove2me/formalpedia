-- Prove2me | Theorems.Thm_MFOTLMon_Monitor_lemma_3_7
-- name    : MFOTLMon.Monitor.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:36.003159+00:00
-- url     : https://prove2.me/theorems/981190e3-c3e4-4602-b5ec-a350a37c3d1a
-- title:
--   Lemma 3.7, p. 15:12 — metric since: r_α^{D̂ᵢ} is regular with the stated characterization, and p_α^{D̂ᵢ} is regular and equals α^(D̄,τ̄,i)
-- statement:
--   Let $\alpha=\beta\,\mathsf S_{[b,b')}\,\gamma$, where $\beta$ and $\gamma$ have the same vector $\bar x=(x_1,\dots,x_n)$ of free variables, and let $r_\alpha^{\hat{\mathcal D}_i}$ and $p_\alpha^{\hat{\mathcal D}_i}$ be given by the construction of §3.4.3. Assume the input structures are automatic with respect to the fixed representation and interpret a binary predicate $\prec$ as $<$. Assume that the relations $p_\varphi^{\hat{\mathcal D}_j}$ are regular and $p_\varphi^{\hat{\mathcal D}_j}=\varphi^{(\bar{\mathcal D},\bar\tau,j)}$ for all $j\le i$ and $\varphi\in\mathit{tsub}(\beta)\cup\mathit{tsub}(\gamma)$. Then:
--
--   1. $r_\alpha^{\hat{\mathcal D}_i}$ is regular and, for all $\bar a\in\mathbb N^n$ and $t\in\mathbb N$,
--   $$
--   (\bar a,t)\in r_\alpha^{\hat{\mathcal D}_i}\iff \exists j\le i:\ t=\tau_i-\tau_j<b',\ \bar a\in\gamma^{(\bar{\mathcal D},\bar\tau,j)},\ \bar a\in\beta^{(\bar{\mathcal D},\bar\tau,k)}\text{ for all }j<k\le i;
--   $$
--   2. $p_\alpha^{\hat{\mathcal D}_i}$ is regular and $p_\alpha^{\hat{\mathcal D}_i}=\alpha^{(\bar{\mathcal D},\bar\tau,i)}$.
--
--   Part 1 says that $r_\alpha$ records, for each tuple, the ages of its still-relevant $\gamma$-witnesses; part 2 is the correctness of the incremental since construction.
--
--   **Formalization Note.** The pair $(\bar a,t)$ is the list $\bar a\mathbin{+\!\!+}[t]$. The same-free-variables hypothesis is the paper's "without loss of generality" assumption of §3.4. The order predicate $\prec$ (§3.1) is a hypothesis because the arithmetic constraint of the construction is defined from it. The construction uses the additive form $t=t'+(\tau_i-\tau_{i-1})$ of the printed constraint.
-- source:
--   Basin, Klaedtke, Müller, Zălinescu, Monitoring metric first-order temporal properties, J. ACM 62(2), Article 15 (2015), p. 15:12, Lemma 3.7 (construction of §3.4.3)

import Mathlib
import Definitions.Def_MFOTLMon_Monitor_Constructions

namespace MFOTLMon.Monitor

/-- Lemma 3.7 (p. 15:12), `α = β S_{[b,b′)} γ` with `free(β) = free(γ)` (WLOG of §3.4). Assume that
the relations `p_φ^{D̂ⱼ}` (here `P φ j`) are regular and equal `φ^{(D̄,τ̄,j)}` for all `j ≤ i` and
`φ ∈ tsub(β) ∪ tsub(γ)`. Then (i) `r_α^{D̂ᵢ}` is regular and, for all `ā ∈ ℕⁿ` and `t ∈ ℕ`,
`(ā, t) ∈ r_α^{D̂ᵢ}` iff there is `j ≤ i` with `t = τᵢ − τⱼ < b′`, `ā ∈ γ^{(D̄,τ̄,j)}` and
`ā ∈ β^{(D̄,τ̄,k)}` for all `j < k ≤ i`; (ii) `p_α^{D̂ᵢ}` is regular and `p_α^{D̂ᵢ} = α^{(D̄,τ̄,i)}`.
`r_α^{D̂ᵢ}` and `p_α^{D̂ᵢ}` are the §3.4.3 constructions `sinceR`, `sinceP` fed with
`β̂^{D̂ⱼ}`, `γ̂^{D̂ⱼ}`. The order `≺` interpreted as `<` (§3.1) is a hypothesis. -/
theorem lemma_3_7 {S : Signature} {Γ : Type} [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S)
    (hD : IsAutomatic rep D) (hlt : HasOrderPred D) (I : Interval) (β γ : Formula S)
    (hfree : free β = free γ) (P : Formula S → ℕ → Set (List ℕ)) (i : ℕ) :
    let B : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) β
    let G : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) γ
    let n := (freeList (Formula.since I β γ)).length
    (∀ j, j ≤ i → ∀ φ ∈ tsub β ++ tsub γ, RegularRel rep (freeList φ).length (P φ j) ∧
      P φ j = satSet D φ j) →
    (RegularRel rep (n + 1) (sinceR D.τ I B G i) ∧
      ∀ a : List ℕ, a.length = n → ∀ t : ℕ,
        (a ++ [t] ∈ sinceR D.τ I B G i ↔
          ∃ j, j ≤ i ∧ t = D.τ i - D.τ j ∧ (t : ℕ∞) < I.hi ∧ a ∈ satSet D γ j ∧
            ∀ k, j < k → k ≤ i → a ∈ satSet D β k)) ∧
    (RegularRel rep n (sinceP I (sinceR D.τ I B G i)) ∧
      sinceP I (sinceR D.τ I B G i) = satSet D (Formula.since I β γ) i) := by sorry

end MFOTLMon.Monitor
