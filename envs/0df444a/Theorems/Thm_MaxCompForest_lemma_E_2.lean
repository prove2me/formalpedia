-- Prove2me | Theorems.Thm_MaxCompForest_lemma_E_2
-- name    : MaxCompForest.lemma_E_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:45.293782+00:00
-- url     : https://prove2.me/theorems/7d7f425f-4094-4fb1-bc4a-b08f9d4b26c9
-- title:
--   Lemma E.2 — physical high-marginal recursion
-- statement:
--   Let $G$ be a connected loopless multigraph with positive conductances, $1\le k\le|V|-1$, and let $0<\alpha\le1$, $0<\xi<1$ be rational, $\rho=\alpha/k^2$, and $M_0>k+k/(\xi\rho)$ an integer. Run the physical recursion: at the forest $S$ of included labels, with $H=G/S$, $j=k-|S|$ and $p_e=K^{(H)}_{ee}$, it returns $S$ if $j=0$, discards infeasible branches, enumerates all $j$-subsets if at most $M_0$ labels remain, stops if $\max_e p_e<\alpha$, and otherwise branches on $\mathcal H=\{e:p_e\ge p_{\max}/j^2\}$ if $|\mathcal H|<M_0$, or enumerates the $j$-subsets of the top $M_0$ labels. Then:
--
--   1. the recursion has depth at most $k$, and each node has fewer than $M_0$ include children;
--   2. either some complete candidate $F$ has $P_G(F\subseteq T)\ge(1-\xi)^k\max_{|J|=k}P_G(J\subseteq T)$, or some all-low node $S$ is a forest contained in a global optimum, with $K^{(H)}_{ee}<\alpha$ for every label $e$ of $H=G/S$;
--   3. for every forest $S$ and every set $J$ of labels of $H=G/S$,
--   $$
--   P_G(S\cup J\subseteq T_G)=P_G(S\subseteq T_G)\det K^{(H)}_J ,
--   $$
--   and $S\cup J$ is a forest exactly when $J$ is a forest in $H$;
--   4. every positive optimal $j$-set of $K^{(H)}$ contains a label of $\mathcal H$.
--
--   The values $\alpha=\varepsilon^2\gamma^2/(2^{30}(k+2)^8)$, $\xi=\varepsilon/(16k)$, $M_0=\lceil k+k/(\xi\rho)\rceil+2$ of (E.2) are a special case. This reduces the search to terminal quotients on which every remaining label has small inclusion probability.
--
--   Differences from the source:
--   - reading: “There is a deterministic branching/enumeration procedure” → the defined function `physNode`, with its depth and fanout stated about that function; reason: a bare existence would hold for full enumeration; the procedure is the one in the proof, pp.38–39
--   - reading: “parameter-bounded fanout” → fewer than $M_0$ include children per node; the $j$-subsets enumerated at a prefix leaf are that leaf's candidates; reason: the proof's own count, pp.38–39, (E.19)
--   - generalization: the lemma's sentence states the dichotomy and depth → Lean adds (E.3) and (E.4) from the proof as clauses; reason: Lemma E.5 uses them; the stated clauses are unchanged
--   - generalization: positive rational conductances → positive real conductances; reason: the argument uses only positivity; rationality matters only for the machine statements, and rational inputs are a special case
--   - generalization: (E.3) for a residual forest $J$ at a node, (E.4) at a node with $p_{\max}\ge\alpha$ and $j=k-|S|$ → (E.3) for every forest $S$ of $G$ and every label set $J$ of $G/S$ (both sides vanish on cyclic $J$), (E.4) for every forest $S$ and every $j\ge1$, without $p_{\max}\ge\alpha$; reason: the proofs on p.38 use neither restriction; at the recursion's nodes these are the printed facts
--   - reading: $k$ with no upper bound in the lemma's sentence → $k\le|V|-1$; reason: the standing convention of Section 3, p.15, “Feasible budgets satisfy 0 ≤ k ≤ n − 1”, which Appendix E inherits
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma E.2, p.38; proof pp.38–39

import Mathlib
import Definitions.Def_MaxCompForest_physTerminals
import Definitions.Def_MaxCompForest_physAllLow
import Definitions.Def_MaxCompForest_inclProb
import Definitions.Def_MaxCompForest_onLabels
import Definitions.Def_MaxCompForest_IsForest
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

/-- **Lemma E.2 (Physical high-marginal recursion)**, in its general form: rational `0 < α ≤ 1`, `0 < ξ < 1`,
`ρ = α/k²`, integer `M0 > k + k/(ξρ)`. The values (E.2) satisfy these conditions (sanity file).
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.38; the procedure and (E.3), (E.4) are in its proof, pp.38–39.

The clauses are: depth at most `k`; fewer than `M0` include children per node; the dichotomy; and the
two displayed facts (E.3), (E.4) that Lemma E.5 uses.

**Formalization Note.** The procedure is the defined `physNode` at `q = 0`, so the depth and fanout clauses
exclude brute force. The budget `k ≤ |V| − 1` is the standing convention of Section 3 (p.15). -/
theorem lemma_E_2 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [LinearOrder E]
    (G : WGraph V E) (hG : G.IsConnected) (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ Fintype.card V)
    (α ξ : ℚ) (M0 : ℕ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (hM0 : (k : ℚ) + k / (ξ * (α / (k : ℚ) ^ 2)) < M0) :
    (∀ d S, S ∈ physNodes G k α M0 0 d → S.card = d ∧ d ≤ k) ∧
    (∀ d S, S ∈ physNodes G k α M0 0 d → ∀ L, physNode G k α M0 0 S = .branch L → L.card < M0) ∧
    ((∃ F ∈ physTerminals G k α M0 0, F.card = k ∧
        ∀ J : Finset E, J.card = k → (1 - (ξ : ℝ)) ^ k * inclProb G J ≤ inclProb G F) ∨
      (∃ S ∈ physAllLow G k α M0 0, IsForest G S ∧
        (∃ Jopt : Finset E, S ⊆ Jopt ∧ Jopt.card = k ∧
          ∀ J : Finset E, J.card = k → inclProb G J ≤ inclProb G Jopt) ∧
        ∀ e : ContractE G S, K (contract G S) e e < α)) ∧
    (∀ S : Finset E, IsForest G S → ∀ J : Finset (ContractE G S),
      inclProb G (S ∪ liftLabels G S J) =
          inclProb G S * (onLabels (K (contract G S)) J).det ∧
        (IsForest G (S ∪ liftLabels G S J) ↔ IsForest (contract G S) J)) ∧
    (∀ S : Finset E, IsForest G S → ∀ j : ℕ, 1 ≤ j → ∀ F : Finset (ContractE G S), F.card = j →
      0 < (onLabels (K (contract G S)) F).det →
      (∀ J : Finset (ContractE G S), J.card = j →
        (onLabels (K (contract G S)) J).det ≤ (onLabels (K (contract G S)) F).det) →
      ∃ e ∈ F, (⨆ e', K (contract G S) e' e') / (j : ℝ) ^ 2 ≤ K (contract G S) e e) := by sorry

end MaxCompForest
