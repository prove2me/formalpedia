-- Prove2me | Theorems.Thm_GlobalUpdatesFO_Upper_lemma_3_14
-- name    : GlobalUpdatesFO.Upper.lemma_3_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:21:22.59468+00:00
-- url     : https://prove2.me/theorems/666e1965-a2ff-442d-8f56-3bc074092991
-- title:
--   Lemma 3.14 — for vertices in different components, the unary k-types determine the pair k-type (k ≥ max(3, maxarity))
-- statement:
--   Let $\Sigma$ be a signature, $k \ge \max(3, \mathrm{maxarity}(\Sigma))$ and $A$ a $\Sigma$-structure. Let $u, u', v, v' \in U(A)$ with $u, v$ in different connected components of $A$ and $u', v'$ in different connected components of $A$. If $\mathrm{tp}^k(u) = \mathrm{tp}^k(u')$ and $\mathrm{tp}^k(v) = \mathrm{tp}^k(v')$, then
--   $$\mathrm{tp}^k(u, v) = \mathrm{tp}^k(u', v') .$$
--
--   The lemma is what makes elements of different components of a flattened structure interchangeable, which drives Lemma 4.10.
--
--   Differences from the source:
--   - encoding: u and v lie in different connected components of A → ¬ A.gaifman.Reachable u v; reason: components of A are those of G(A) (p. 24)
--   - encoding: a finite Σ-structure with universe U(A), relation names of Σ with their arities → Structure σ U on a finite type U : Type, Σ the list of arities, relation names 0, …, |Σ|−1; reason: Lean convention; every finite structure is of this form up to renaming
--   - encoding: formulas of FO^k[Σ] with r free variables x̄, up to renaming of bound variables → named-variable Formula over ℕ; IsFOk σ k r φ: WF, free variables among x_0, …, x_{r−1}, and |vars(φ) ∪ {0, …, r−1}| ≤ k; reason: the paper's definition (p. 17) with the free tuple fixed to x_0, …, x_{r−1}; renaming bound variables changes no type
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), p. 24, Lemma 3.14

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula

namespace GlobalUpdatesFO.Upper

theorem lemma_3_14 (σ : Signature) (k : ℕ) (hk : max 3 σ.maxarity ≤ k)
    (U : Type) [Fintype U] (A : Structure σ U) (u u' v v' : U)
    (huv : ¬ A.gaifman.Reachable u v) (huv' : ¬ A.gaifman.Reachable u' v')
    (hu : tp k A ![u] = tp k A ![u']) (hv : tp k A ![v] = tp k A ![v']) :
    tp k A ![u, v] = tp k A ![u', v'] := by sorry

end GlobalUpdatesFO.Upper
