-- Prove2me | Theorems.Thm_MaxCompForest_lemma_E_3
-- name    : MaxCompForest.lemma_E_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:37:42.076233+00:00
-- url     : https://prove2.me/theorems/79f26288-ac30-426e-b8ee-60176dd26b97
-- title:
--   Lemma E.3 — higher normalized eigenvalues under physical contraction
-- statement:
--   Let $G$ be a connected loopless multigraph with positive conductances, $S$ a forest of its labels, and $H=G/S$ the loopless labelled quotient, with its own weighted degrees. If $|V(H)|\ge2$, then
--   $$
--   \lambda_j(N_H)\ge\lambda_j(N_G)\qquad(1\le j\le|V(H)|).
--   $$
--   If moreover $G$ is simple and $|S|\le k$, then every quotient vertex contains at most $k+1$ original vertices, and every pair of quotient vertices has at most $(k+1)^2$ original labels.
--
--   So contraction preserves the spectral promise, and the labels per pair stay bounded independently of the conductances.
--
--   Differences from the source:
--   - encoding: $\lambda_j$, $1\le j\le|V(H)|$ → `lam … (j − 1)` with `j − 1 < |V(H)|`; reason: a 0-based index
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma E.3, p.39

import Mathlib
import Definitions.Def_MaxCompForest_lam
import Definitions.Def_MaxCompForest_deg
import Definitions.Def_MaxCompForest_contract
import Definitions.Def_MaxCompForest_IsForest
import Definitions.Def_MaxCompForest_compVerts
import Definitions.Def_MaxCompForest_PairMult
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

/-- **Lemma E.3 (Higher normalized eigenvalues under physical contraction).**
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.39.

**Formalization Note.** `lam` is 0-based: the printed `λ_j`, `1 ≤ j ≤ |V(H)|`, is `lam … (j − 1)`. Degrees are
each graph's own. -/
theorem lemma_E_3 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (hG : G.IsConnected) (S : Finset E) (hS : IsForest G S)
    (hH : 2 ≤ Fintype.card (ContractV G S)) :
    (∀ j, j < Fintype.card (ContractV G S) →
      lam G (deg G) j ≤ lam (contract G S) (deg (contract G S)) j) ∧
    (G.IsSimple → ∀ k : ℕ, S.card ≤ k →
      (∀ C : ContractV G S, (compVerts G S C).card ≤ k + 1) ∧
        PairMult (contract G S) ((k + 1) ^ 2)) := by sorry

end MaxCompForest
