-- Prove2me | Theorems.Thm_IncrementalER_levels_p39
-- name    : IncrementalER.levels_p39
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:08:01.305509+00:00
-- url     : https://prove2.me/theorems/c70cedc2-e047-4f63-b9b9-c3c4a1a6f352
-- title:
--   Proof of Theorem 1.1, p.39 — $\ell$ levels of $(1\pm\frac{\varepsilon}{100\ell})$-approximate Schur complements give $(1\pm\varepsilon)$-approximate energies
-- statement:
--   Let $\ell\ge1$, $0<\varepsilon<1/2$, and let $G_0,\dots,G_\ell$ be graphs on nested nonempty vertex sets $V_0\supseteq V_1\supseteq\dots\supseteq V_\ell$, each $G_i$ connected on $V_i$, such that for every $i<\ell$
--
--   $$\Big(1-\frac{\varepsilon}{100\ell}\Big)SC(G_i,V_{i+1})\preceq G_{i+1}\preceq\Big(1+\frac{\varepsilon}{100\ell}\Big)SC(G_i,V_{i+1}),$$
--
--   where $H\preceq G$ means that $L_G-L_H$ is positive semidefinite. Then:
--
--   1. $(1-\varepsilon/8)\,SC(G_0,V_\ell)\preceq G_\ell\preceq(1+\varepsilon/8)\,SC(G_0,V_\ell)$;
--   2. for every demand $d$ supported on $V_\ell$ with $d^\top\mathbf 1=0$ and every $E$ with $(1-\varepsilon/16)E\le d^\top L_{G_0}^\dagger d\le E$ (the bounds (23) with $E=d^\top L_{\hat G}^\dagger d$),
--   $$\frac{1-\varepsilon/16}{1+\varepsilon/8}E\le d^\top L_{G_\ell}^\dagger d\le\frac{1}{1-\varepsilon/8}E,$$
--   and these bounds lie within $[(1-\varepsilon)E,(1+\varepsilon)E]$.
--
--   This is the accuracy part of the proof of Theorem 1.1: the answer computed on the last level of the hierarchy is a $(1\pm\varepsilon)$-approximation.
--
--   Differences from the source:
--   - encoding: G = (V, E, c) an undirected capacitated multigraph (p.10) → a symmetric nonnegative conductance function with zero diagonal (parallel capacities added, no loops); reason: the Laplacian, effective resistances, leverage degrees and the random walk are unchanged by merging parallel edges; the paper's edges (u, v) join two vertices, and the source never uses loops
--   - encoding: G_i a graph with vertex set V_i, SC(G_i, V_{i+1}) a graph on V_{i+1} → G_i a conductance function on the common vertex type supported on V_i and connected there; SC eliminates V_i \ V_{i+1} (scCondRel); reason: the same graphs, with vertices outside V_i isolated
--   - encoding: "conditioning on the success of all levels" → every level's sandwich as a hypothesis; reason: the statement is the deterministic consequence of success at every level
--   - generalization: E = d⊤L†_Ĝ d, with (23) relating it to G = G_0 → any E with (1 − ε/16)E ≤ d⊤L†_{G_0} d ≤ E; reason: (23) gives these bounds for E = d⊤L†_Ĝ d
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), proof of Theorem 1.1, "Spectral approximation and query estimations", p.39; Fact 3.4, p.11; ⪯, p.10

import Mathlib
import Definitions.Def_IncrementalER_scCond

namespace IncrementalER

/-- **Level composition** of the sparsification hierarchy, proof of Theorem 1.1.

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), proof of Theorem 1.1,
"Spectral approximation and query estimations", p.39; Fact 3.4, p.11; `A ⪯ B`, p.10.

Let `ℓ ≥ 1`, `0 < ε < 1/2`, and let `G_0, …, G_ℓ` be graphs on nested nonempty vertex sets
`V_0 ⊇ V_1 ⊇ ⋯ ⊇ V_ℓ`, each `G_i` connected on `V_i`, with
`(1 − ε/(100ℓ)) SC(G_i, V_{i+1}) ⪯ G_{i+1} ⪯ (1 + ε/(100ℓ)) SC(G_i, V_{i+1})` for `i < ℓ`. Then
1. `(1 − ε/8) SC(G_0, V_ℓ) ⪯ G_ℓ ⪯ (1 + ε/8) SC(G_0, V_ℓ)`;
2. for every demand `d` supported on `V_ℓ` with `d⊤1 = 0` and every `E` with
   `(1 − ε/16) E ≤ d⊤L†_{G_0} d ≤ E` (the bounds (23) with `E = d⊤L†_Ĝ d`):
   `(1 − ε/16)/(1 + ε/8) E ≤ d⊤L†_{G_ℓ} d ≤ E/(1 − ε/8)`, and these lie within
   `[(1 − ε) E, (1 + ε) E]`.

**Formalization Note.** Every `G_i` is a conductance function on the common vertex type, supported
on `V_i` (`IsConnectedOn`); `SC(G_i, V_{i+1})` eliminates `V_i \ V_{i+1}` (`scCondRel`). `H ⪯ G`
means `L_G − L_H` is positive semidefinite (p.10). The induction "conditioning on the success of all
levels" is the hypothesis that every level satisfies its sandwich. -/
theorem levels_p39 {V : Type*} [Fintype V] [DecidableEq V] (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (ε : ℝ)
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (G : ℕ → V → V → ℝ) (Vs : ℕ → Finset V)
    (hG : ∀ i ≤ ℓ, IsGraph (G i)) (hconn : ∀ i ≤ ℓ, IsConnectedOn (G i) (Vs i))
    (hnest : ∀ i < ℓ, Vs (i + 1) ⊆ Vs i) (hne : (Vs ℓ).Nonempty)
    (hlow : ∀ i < ℓ, (lap (G (i + 1)) -
      (1 - ε / (100 * ℓ)) • lap (scCondRel (G i) (Vs i) (Vs (i + 1)))).PosSemidef)
    (hupp : ∀ i < ℓ, ((1 + ε / (100 * ℓ)) • lap (scCondRel (G i) (Vs i) (Vs (i + 1))) -
      lap (G (i + 1))).PosSemidef) :
    ((lap (G ℓ) - (1 - ε / 8) • lap (scCondRel (G 0) (Vs 0) (Vs ℓ))).PosSemidef ∧
        ((1 + ε / 8) • lap (scCondRel (G 0) (Vs 0) (Vs ℓ)) - lap (G ℓ)).PosSemidef) ∧
      ∀ d : V → ℝ, (∀ x, x ∉ Vs ℓ → d x = 0) → ∑ x, d x = 0 → ∀ E : ℝ,
        (1 - ε / 16) * E ≤ energy (lap (G 0)) d → energy (lap (G 0)) d ≤ E →
        ((1 - ε / 16) / (1 + ε / 8) * E ≤ energy (lap (G ℓ)) d ∧
          energy (lap (G ℓ)) d ≤ E / (1 - ε / 8)) ∧
        ((1 - ε) * E ≤ energy (lap (G ℓ)) d ∧ energy (lap (G ℓ)) d ≤ (1 + ε) * E) := by sorry

end IncrementalER
