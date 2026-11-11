-- Prove2me | Theorems.Thm_GlobalUpdatesFO_Upper_lemma_4_12
-- name    : GlobalUpdatesFO.Upper.lemma_4_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:22:13.862433+00:00
-- url     : https://prove2.me/theorems/c5637f7a-29ef-4383-9753-98756242c7fe
-- title:
--   Lemma 4.12 — the ancestor preorder ≼^k_A of the tight decomposition is defined by a computable FO formula Ψ_{Σ,k,D}(x, y)
-- statement:
--   For all integers $\nu, k, D \ge 1$ with $k \ge k_{4.11}(\nu,D)$ and all signatures $\Sigma$ with $\mathrm{maxarity}(\Sigma) \le \nu$, one can compute a formula $\Psi_{\Sigma,k,D}(x,y)$ of $\mathrm{FO}[\Sigma]$ such that for every $\Sigma$-structure $A$ with $\mathrm{td}(A) \le D$ and all $u, v \in U(A)$
--   $$A \models \Psi_{\Sigma,k,D}(u,v) \iff u \preccurlyeq^k_A v .$$
--
--   Tight decompositions are thus first-order definable, which is what bounds the first-order index of the residual structures used in the potential.
--
--   **Formalization Note** $\preccurlyeq^k_A$ is taken in some tight $k$-robust decomposition of $A$ (unique by Lemma 4.11 above the threshold).
--
--   Differences from the source:
--   - reading: k ≥ k_{4.11}(ν, D), the threshold of Lemma 4.11 → k ≥ k′(ν, D) for a computable k′ existentially quantified in this lemma; reason: k_{4.11} is only defined by the existential of Lemma 4.11; all these thresholds are monotone (they hold for every larger k), so one joint threshold exists iff each lemma has its own
--   - encoding: we can compute a formula Ψ_{Σ,k,D}(x, y) of FO[Σ] → ∃ F : List ℕ × ℕ × ℕ → List ℕ computable with F(Σ, k, D) = code of Ψ, Ψ.WF σ, free variables among x_0, x_1; reason: 'computable' read as Mathlib Computable on the list codes of signatures (lists of arities) and formulas (prefix codes)
--   - generalization: Ψ computed from the given ν, k, D and Σ → Ψ computed from (Σ, k, D) alone; reason: the paper's notation Ψ_{Σ,k,D} and construction do not use ν; a computation from (Σ, k, D) is in particular one from (ν, k, D, Σ)
--   - reading: u ≼^k_A v in the tight k-robust decomposition of A → Prec k A u v: in some tight k-robust decomposition, bag⁻¹(u) is an ancestor of bag⁻¹(v); reason: the tight decomposition exists and is unique up to renaming nodes (Lemma 4.11)
--   - encoding: a finite Σ-structure with universe U(A), relation names of Σ with their arities → Structure σ U on a finite type U : Type, Σ the list of arities, relation names 0, …, |Σ|−1; reason: Lean convention; every finite structure is of this form up to renaming
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), p. 32, Lemma 4.12

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula
import Definitions.Def_GlobalUpdatesFO_Upper_Flattening
import Definitions.Def_GlobalUpdatesFO_Upper_Robust

namespace GlobalUpdatesFO.Upper

theorem lemma_4_12 :
    ∃ (k' : ℕ × ℕ → ℕ) (F : List ℕ × ℕ × ℕ → List ℕ), Computable k' ∧ Computable F ∧
      ∀ (ν k D : ℕ), 1 ≤ ν → 1 ≤ k → 1 ≤ D → k' (ν, D) ≤ k →
        ∀ σ : Signature, σ.maxarity ≤ ν →
          ∃ Ψ : Formula, F (σ, k, D) = Ψ.code ∧ Ψ.WF σ ∧ Ψ.freeVars ⊆ Finset.range 2 ∧
            ∀ (U : Type) [Fintype U] (A : Structure σ U), A.td ≤ D →
              ∀ u v : U, Sat A Ψ ![u, v] ↔ Prec k A u v := by sorry

end GlobalUpdatesFO.Upper
