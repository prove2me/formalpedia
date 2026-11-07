-- Prove2me | Theorems.Thm_MCPoise_lemma_2_10
-- name    : MCPoise.lemma_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:31:47.786782+00:00
-- url     : https://prove2.me/theorems/24ee21e2-c95c-4ebd-ae9d-a4fb13faca2d
-- title:
--   Lemma 2.10 — aggregate fractional load, $\le 8\hat x_{e,j}$ per edge and $\le 8L_\Delta$ per vertex
-- statement:
--   With $(\hat x, \hat f)$ feasible for Multiroot-LP and the data of Stage 1 for each nonempty group:
--
--   **Lemma 2.10.** For every $j \in [\mu]$ and every edge $e \in E$,
--   $$\sum_{t \in S'_j} \sum_{p \in Q^t_j,\, e \in E(p)} y^{j,t}_p \le 8 \hat x_{e,j}. \tag{1}$$
--   Consequently, for every vertex $v \in V$,
--   $$\sum_{e \in \delta_G(v)} \sum_{j \in [\mu]} \sum_{t \in S'_j} \sum_{p \in Q^t_j,\, e \in E(p)} y^{j,t}_p \le 8 L_\Delta. \tag{2}$$
--   Here $Q^t_j$ holds the surviving paths and $y$ the scaled weights.
--
--   Differences from the source:
--   - generalization: the packing of size ½Σλ from Theorem 2.8 → any S⁺_j-path-packing with such selections; reason: the proof does not read the size of the packing
--   - encoding: parameter L′_d → a natural number; reason: it bounds a number of edges, and the only L′_d the paper uses is the integer ρ²L_d
--   - reading: scale corresponding y values down so the sum is 1 → each surviving path has weight 1/|surviving paths|; reason: every y is 4/C before scaling, so uniform scaling is the page's operation
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.10, pp.18–19

import Mathlib
import Definitions.Def_MCPoise_MultirootLP
import Definitions.Def_MCPoise_IsStage1

namespace MCPoise

open scoped Classical in
/-- **Lemma 2.10 (aggregate fractional load).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.10, pp.18–19: "For every j ∈ [µ] and every edge e ∈ E, Σ_{t∈S′_j} Σ_{p∈Q^t_j, e∈E(p)} y^{j,t}_p ≤ 8x̂_{e,j}. (1) Consequently, for every vertex v ∈ V,
Σ_{e∈δ_G(v)} Σ_{j∈[µ]} Σ_{t∈S′_j} Σ_{p∈Q^t_j, e∈E(p)} y^{j,t}_p ≤ 8L_∆. (2)"

`Q^t_j` holds the surviving paths and `y` the weights after the scaling of p.18. Groups with empty `S_j` are skipped, as on p.17, and contribute `0`.

**Formalization Note.** `e ∈ E(p)` means a copy of `e` is an edge of `p`, read from the vertex list. -/
theorem lemma_2_10 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {μ : ℕ} (r : Fin μ → V)
    (S : Fin μ → Finset V) (LΔ : ℝ) (Lp : ℕ) (x : Sym2 V → Fin μ → ℝ) (f : Fin μ → V → List V → ℝ)
    (hLP : MultirootLP G r S LΔ Lp x f) (C : Fin μ → ℕ) (M : Fin μ → MGraph V)
    (Q : Fin μ → List (MPath V)) (Qt : ∀ j, V → Finset (Fin (Q j).length))
    (hst : ∀ j, (S j).Nonempty →
      IsStage1 G (r j) (S j) Lp (f j) (fun e => x e j) (C j) (M j) (Q j) (Qt j)) :
    (∀ j, ∀ e ∈ G.edgeSet,
      ∑ t ∈ Sprime (S j) Lp (C j) (Q j) (Qt j), ∑ q ∈ surv Lp (Q j) (Qt j) t,
        (if e ∈ pEdges (Q j)[q].vs then yWeight Lp (Q j) (Qt j) t else 0) ≤ 8 * x e j) ∧
    ∀ v, ∑ e ∈ delta G v, ∑ j, ∑ t ∈ Sprime (S j) Lp (C j) (Q j) (Qt j),
      ∑ q ∈ surv Lp (Q j) (Qt j) t,
        (if e ∈ pEdges (Q j)[q].vs then yWeight Lp (Q j) (Qt j) t else 0) ≤ 8 * LΔ := by sorry

end MCPoise
