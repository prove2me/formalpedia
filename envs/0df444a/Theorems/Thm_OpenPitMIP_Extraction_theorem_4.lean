-- Prove2me | Theorems.Thm_OpenPitMIP_Extraction_theorem_4
-- name    : OpenPitMIP.Extraction.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:44.337489+00:00
-- url     : https://prove2.me/theorems/5291d9b7-0149-4020-9c0d-44e8c3dcbc41
-- title:
--   Theorem 4, p. 1433 — clique and lifted clique cuts are valid on pairwise f-incompatible (PCPSP-F) or p-incompatible (PCPSP-P) clusters
-- statement:
--   Consider an instance of the PCPSP-C satisfying the standing assumptions, a period $t\in\mathcal T$, and a set $K=\{c_1,\dots,c_k\}$ of clusters. Consider the **clique inequality**
--   $$\sum_{i=1}^{k}w_{c_i,t}\le 1.\tag{23}$$
--   Then:
--
--   1. if $c_1,\dots,c_k$ are pairwise f-incompatible in time $t$, (23) holds at every point feasible for the PCPSP-F that satisfies the mining capacity rows (8);
--   2. if $c_1,\dots,c_k$ are pairwise p-incompatible in time $t$, (23) holds at every point feasible for the PCPSP-P that satisfies (8);
--   3. if a cluster $c$ satisfies $c\prec c_i$ for $i=1,\dots,k$ and $c_1,\dots,c_k$ are pairwise f-incompatible, the **lifted clique inequality**
--   $$\sum_{i=1}^{k}w_{c_i,t}\le w_{c,t}$$
--   holds at every point feasible for the PCPSP-F that satisfies (8);
--   4. the same lifted inequality holds at every point feasible for the PCPSP-P that satisfies (8) when $c_1,\dots,c_k$ are pairwise p-incompatible.
--
--   Here $c_1,c_2$ (neither preceding the other) are f-incompatible in time $t$ if $q(cl(\{c_1,c_2\}))>Q_t$, and p-incompatible if $q(cl(\{c_1,c_2\})\setminus\{c_1,c_2\})>Q_t$, where $Q_t=\sum_{t'=1}^{t}U_{t'}$. Clique cuts extend the classical clique inequalities of precedence-constrained knapsack problems to the multi-period clustered setting, including partial integrality.
--
--   **Formalization Note** "Pairwise" ranges over distinct members of the finite set $K$; $K$ may be empty or a singleton, as the page allows. The closure of a pair is $cl(c_1)\cup cl(c_2)$. Validity is stated as for Theorems 2–3: for every feasible point with the given integrality condition whose mining capacity rows (8) hold; the cuts are not claimed for the LP relaxation.
-- source:
--   Oper. Res. 68(5), Theorem 4, (23), p. 1433

import Mathlib
import Definitions.Def_OpenPitMIP_Extraction_Setting

namespace OpenPitMIP.Extraction

/-- Theorem 4 (clique and lifted clique cuts), p. 1433. For a set `K = {c₁, …, c_k}` of clusters
and a period `t`, the clique inequality (23) `∑_{c ∈ K} w_{c,t} ≤ 1` is valid for the PCPSP-F if
the clusters of `K` are pairwise f-incompatible in time `t`, and for the PCPSP-P if they are
pairwise p-incompatible; and for every cluster `c₀` with `c₀ ≺ c` for all `c ∈ K`, the lifted
inequality `∑_{c ∈ K} w_{c,t} ≤ w_{c₀,t}` is valid under the same conditions. "Valid" means: at
every feasible point whose mining capacity rows (8) hold. -/
theorem theorem_4 {B D C : Type} [Fintype B] [Fintype D] [Fintype C] [DecidableEq C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (t : Fin T) (K : Finset C) :
    ((∀ c₁ ∈ K, ∀ c₂ ∈ K, c₁ ≠ c₂ → I.FIncompatible t c₁ c₂) →
      ∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ),
        I.Feasible .F x y → I.MiningCap y → ∑ c ∈ K, PCPSPC.cum x c t ≤ 1) ∧
    ((∀ c₁ ∈ K, ∀ c₂ ∈ K, c₁ ≠ c₂ → I.PIncompatible t c₁ c₂) →
      ∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ),
        I.Feasible .P x y → I.MiningCap y → ∑ c ∈ K, PCPSPC.cum x c t ≤ 1) ∧
    (∀ c₀ : C, (∀ c ∈ K, I.cprec c₀ c) →
      (∀ c₁ ∈ K, ∀ c₂ ∈ K, c₁ ≠ c₂ → I.FIncompatible t c₁ c₂) →
      ∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ),
        I.Feasible .F x y → I.MiningCap y →
          ∑ c ∈ K, PCPSPC.cum x c t ≤ PCPSPC.cum x c₀ t) ∧
    (∀ c₀ : C, (∀ c ∈ K, I.cprec c₀ c) →
      (∀ c₁ ∈ K, ∀ c₂ ∈ K, c₁ ≠ c₂ → I.PIncompatible t c₁ c₂) →
      ∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ),
        I.Feasible .P x y → I.MiningCap y →
          ∑ c ∈ K, PCPSPC.cum x c t ≤ PCPSPC.cum x c₀ t) := by sorry

end OpenPitMIP.Extraction
