-- Prove2me | Theorems.Thm_GlobalUpdatesFO_Upper_lemma_3_6
-- name    : GlobalUpdatesFO.Upper.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:21:11.625195+00:00
-- url     : https://prove2.me/theorems/9d6f3272-05f0-413b-82b6-c852733e2284
-- title:
--   Lemma 3.6 — treedepth ≤ D is FO^k-definable (k computable from ν, D), and connectivity is FO^k-definable on TD_D for k ≥ max(3, ν)
-- statement:
--   Let $\nu, D \ge 1$ and let $\Sigma$ be a signature with $\mathrm{maxarity}(\Sigma) \le \nu$.
--
--   1. There is an integer $k$, computable from $\nu$ and $D$, such that some sentence of $\mathrm{FO}^k[\Sigma]$ is satisfied exactly in the $\Sigma$-structures of treedepth at most $D$.
--   2. There is a formula $\Psi_{\mathrm{conn}}(x,y)$, depending only on $\Sigma$ and $D$, which lies in $\mathrm{FO}^k[\Sigma]$ for every $k \ge \max(3,\nu)$ and satisfies, for every $\Sigma$-structure $A$ of treedepth at most $D$ and all $u, v \in U(A)$,
--   $$u, v \text{ lie in the same connected component of } A \iff A \models \Psi_{\mathrm{conn}}(u,v).$$
--
--   These are the standard first-order expressibility facts the paper uses throughout: the treedepth bound itself is a sentence, and on bounded treedepth connectivity is a bounded-variable formula.
--
--   **Formalization Note** "In the same connected component" is reachability in $G(A)$. The computable integer is a computable function $k(\nu, D)$, quantified before $\nu$, $D$ and $\Sigma$.
--
--   Differences from the source:
--   - encoding: an integer k computable from ν and D → ∃ kf : ℕ × ℕ → ℕ computable, the sentence in FO^{kf(ν, D)}[Σ]; reason: 'computable' read as Mathlib Computable on the list codes of signatures (lists of arities) and formulas (prefix codes)
--   - reading: Ψ_conn ∈ FO^k[Σ] for a given k ≥ max(3, ν), depending only on Σ and D → Ψ is chosen after Σ and D and before ν and k, and lies in FO^k[Σ] for every ν ≥ max(1, maxarity Σ) and every k ≥ max(3, ν); reason: the literal meaning of 'depending only on Σ and D'
--   - encoding: u, v in the same connected component of A → A.gaifman.Reachable u v; reason: components of A are those of G(A) (p. 24)
--   - encoding: a finite Σ-structure with universe U(A), relation names of Σ with their arities → Structure σ U on a finite type U : Type, Σ the list of arities, relation names 0, …, |Σ|−1; reason: Lean convention; every finite structure is of this form up to renaming
--   - encoding: formulas of FO^k[Σ] with r free variables x̄, up to renaming of bound variables → named-variable Formula over ℕ; IsFOk σ k r φ: WF, free variables among x_0, …, x_{r−1}, and |vars(φ) ∪ {0, …, r−1}| ≤ k; reason: the paper's definition (p. 17) with the free tuple fixed to x_0, …, x_{r−1}; renaming bound variables changes no type
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), p. 21, Lemma 3.6

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula

namespace GlobalUpdatesFO.Upper

theorem lemma_3_6 :
    (∃ kf : ℕ × ℕ → ℕ, Computable kf ∧
      ∀ (ν D : ℕ), 1 ≤ ν → 1 ≤ D → ∀ σ : Signature, σ.maxarity ≤ ν →
        ∃ φ : Formula, IsFOk σ (kf (ν, D)) 0 φ ∧
          ∀ (U : Type) [Fintype U] (A : Structure σ U),
            Sat A φ (Fin.elim0 : Fin 0 → U) ↔ A.td ≤ D) ∧
    (∀ (D : ℕ) (σ : Signature), 1 ≤ D →
      ∃ Ψ : Formula, ∀ ν : ℕ, 1 ≤ ν → σ.maxarity ≤ ν → ∀ k : ℕ, max 3 ν ≤ k →
        IsFOk σ k 2 Ψ ∧
        ∀ (U : Type) [Fintype U] (A : Structure σ U), A.td ≤ D →
          ∀ u v : U, A.gaifman.Reachable u v ↔ Sat A Ψ ![u, v]) := by sorry

end GlobalUpdatesFO.Upper
