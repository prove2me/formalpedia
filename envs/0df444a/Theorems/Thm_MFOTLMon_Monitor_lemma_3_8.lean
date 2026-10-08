-- Prove2me | Theorems.Thm_MFOTLMon_Monitor_lemma_3_8
-- name    : MFOTLMon.Monitor.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:36.081143+00:00
-- url     : https://prove2.me/theorems/6e7b2fe7-20a1-4b8c-bd44-276a3fef7a50
-- title:
--   Lemma 3.8, pp. 15:13–15:14 (repaired) — bounded until: characterizations of r_α^{D̂ᵢ} and s_α^{D̂ᵢ}, and p_α^{D̂ᵢ} is regular and equals α^(D̄,τ̄,i)
-- statement:
--   Let $\alpha=\beta\,\mathsf U_{[b,b')}\,\gamma$ with $b'\in\mathbb N$, where $\beta$ and $\gamma$ have the same vector $\bar x=(x_1,\dots,x_n)$ of free variables, let $\ell_i$ be the lookahead offset, and let $r_\alpha^{\hat{\mathcal D}_i}$, $s_\alpha^{\hat{\mathcal D}_i}$, $p_\alpha^{\hat{\mathcal D}_i}$ be given by the (repaired) construction of §3.4.4. Assume the input structures are automatic with respect to the fixed representation and interpret a binary predicate $\prec$ as $<$, and that the relations $p_\varphi^{\hat{\mathcal D}_k}$ are regular and $p_\varphi^{\hat{\mathcal D}_k}=\varphi^{(\bar{\mathcal D},\bar\tau,k)}$ for all $k\le i+\ell_i$ and $\varphi\in\mathit{tsub}(\beta)\cup\mathit{tsub}(\gamma)$. Then:
--
--   1. $r_\alpha^{\hat{\mathcal D}_i}$ is regular and, for all $\bar a\in\mathbb N^n$ and $j\in\mathbb N$,
--   $$(\bar a,j)\in r_\alpha^{\hat{\mathcal D}_i}\iff j\le\ell_i\ \text{and}\ \bar a\in\beta^{(\bar{\mathcal D},\bar\tau,i+k)}\text{ for all }j\le k\le\ell_i;$$
--   2. $s_\alpha^{\hat{\mathcal D}_i}$ is regular and, for all $\bar a\in\mathbb N^n$ and $j,j',t\in\mathbb N$,
--   $$(\bar a,j,j',t)\in s_\alpha^{\hat{\mathcal D}_i}\iff j\le j',\ t=\tau_{i+j'}-\tau_i\in[b,b'),\ \bar a\in\gamma^{(\bar{\mathcal D},\bar\tau,i+j')},\ \bar a\in\beta^{(\bar{\mathcal D},\bar\tau,i+k)}\text{ for all }j\le k<j';$$
--   3. $p_\alpha^{\hat{\mathcal D}_i}$ is regular and $p_\alpha^{\hat{\mathcal D}_i}=\alpha^{(\bar{\mathcal D},\bar\tau,i)}$.
--
--   This is the correctness of the incremental construction for the bounded until operator, the only future operator with an unbounded number of time points to wait for.
--
--   **Formalization Note.** The statement is repaired with respect to the page in three places. The construction carries repairs R1 and R2 (see the `Constructions` definition): the printed construction is not correct, already in the paper's own example of §3.5. In part 1 the page writes "$\bar a\in\mathbb N$", read here as $\mathbb N^n$; and the page has no bound on $j$, so that for $j>\ell_i$ its right-hand side holds vacuously while the relation contains no such pair; the bound $j\le\ell_i$ is added to the right-hand side. Tuples are lists $\bar a\mathbin{+\!\!+}[j]$, $\bar a\mathbin{+\!\!+}[j,j',t]$. $b'$ is the finite upper bound of $I$ (hypothesis `I.hi = b'`).
-- source:
--   Basin, Klaedtke, Müller, Zălinescu, Monitoring metric first-order temporal properties, J. ACM 62(2), Article 15 (2015), pp. 15:13–15:14, Lemma 3.8 (construction of §3.4.4, repaired; Printed slips 1–4)

import Mathlib
import Definitions.Def_MFOTLMon_Monitor_Constructions

namespace MFOTLMon.Monitor

/-- Lemma 3.8 (pp. 15:13–15:14, repaired), `α = β U_{[b,b′)} γ` with `b′ ∈ ℕ` and
`free(β) = free(γ)` (WLOG of §3.4). Let `ℓᵢ` be the lookahead offset. Assume that the relations
`p_φ^{D̂ₖ}` (here `P φ k`) are regular and equal `φ^{(D̄,τ̄,k)}` for all `k ≤ i + ℓᵢ` and
`φ ∈ tsub(β) ∪ tsub(γ)`. Then, for the repaired §3.4.4 construction (`untilRS`, `untilP`):
(i) `r_α^{D̂ᵢ}` is regular and, for all `ā ∈ ℕⁿ` and `j ∈ ℕ`, `(ā, j) ∈ r_α^{D̂ᵢ}` iff `j ≤ ℓᵢ` and
`ā ∈ β^{(D̄,τ̄,i+k)}` for all `j ≤ k ≤ ℓᵢ`;
(ii) `s_α^{D̂ᵢ}` is regular and, for all `ā ∈ ℕⁿ` and `j, j′, t ∈ ℕ`, `(ā, j, j′, t) ∈ s_α^{D̂ᵢ}` iff
`j ≤ j′`, `t = τ_{i+j′} − τᵢ ∈ [b, b′)`, `ā ∈ γ^{(D̄,τ̄,i+j′)}` and `ā ∈ β^{(D̄,τ̄,i+k)}` for all
`j ≤ k < j′`;
(iii) `p_α^{D̂ᵢ}` is regular and `p_α^{D̂ᵢ} = α^{(D̄,τ̄,i)}`. -/
theorem lemma_3_8 {S : Signature} {Γ : Type} [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S)
    (hD : IsAutomatic rep D) (hlt : HasOrderPred D) (I : Interval) (b' : ℕ) (hb' : I.hi = b')
    (β γ : Formula S) (hfree : free β = free γ) (P : Formula S → ℕ → Set (List ℕ)) (i : ℕ) :
    let B : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) β
    let G : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) γ
    let n := (freeList (Formula.until I β γ)).length
    let ℓ := lookahead D b' i
    let RS := untilRS D I B G i
    (∀ k, k ≤ i + ℓ → ∀ φ ∈ tsub β ++ tsub γ, RegularRel rep (freeList φ).length (P φ k) ∧
      P φ k = satSet D φ k) →
    (RegularRel rep (n + 1) RS.1 ∧
      ∀ a : List ℕ, a.length = n → ∀ j : ℕ,
        (a ++ [j] ∈ RS.1 ↔ j ≤ ℓ ∧ ∀ k, j ≤ k → k ≤ ℓ → a ∈ satSet D β (i + k))) ∧
    (RegularRel rep (n + 3) RS.2 ∧
      ∀ a : List ℕ, a.length = n → ∀ j j' t : ℕ,
        (a ++ [j, j', t] ∈ RS.2 ↔
          j ≤ j' ∧ t = D.τ (i + j') - D.τ i ∧ I.Mem t ∧ a ∈ satSet D γ (i + j') ∧
            ∀ k, j ≤ k → k < j' → a ∈ satSet D β (i + k))) ∧
    (RegularRel rep n (untilP RS.2) ∧ untilP RS.2 = satSet D (Formula.until I β γ) i) := by sorry

end MFOTLMon.Monitor
