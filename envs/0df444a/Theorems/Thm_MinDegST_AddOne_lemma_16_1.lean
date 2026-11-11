-- Prove2me | Theorems.Thm_MinDegST_AddOne_lemma_16_1
-- name    : MinDegST.AddOne.lemma_16_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:53:07.35017+00:00
-- url     : https://prove2.me/theorems/ef4b52d9-9392-4028-998d-85896ec8a84e
-- title:
--   Lemma 16.1 — Ω(f) augmenting chains in Ô(m) time
-- statement:
--   There are one deterministic word-RAM program, a word-width constant and a universal constant $c>0$, fixed before $\varepsilon$, such that for every $\varepsilon>0$ there is $K_\varepsilon>0$ with: for every connected graph $G$ with $n$ nodes and $m$ edges, threshold $k<n$ for which $G$ has a spanning tree of maximum degree at most $k$, and forest $F$ of $G$ of maximum degree at most $k+1$ with $f\ge2$ components, on input $(G,k,F)$ the program halts within
--   $$K_\varepsilon\cdot m\cdot n^{\varepsilon}+K_\varepsilon$$
--   steps and outputs a $\theta$-molecular decomposition $M$ of $F$ with $\theta=\lceil10n/f\rceil$, its reducible regions $\mathcal R$, and at least $c\cdot f$ distinct augmenting chains with respect to $(F,M,\mathcal R)$.
--
--   The proof uses one exact maximum-flow computation (Lemma 13.3, the external input `DirectedGlobalMincut.Sampling.maximum_flow_external`).
--
--   Differences from the source:
--   - generalization: the degree bound is Δ⋆(G) (feasible = max degree ≤ Δ⋆ + 1, slack = degree ≤ Δ⋆, saturated = Δ⋆ + 1) → any threshold k < n for which G has a spanning tree of maximum degree ≤ k, with feasible/slack/saturated relative to k; reason: Part I's convention (p. 4); the case k = Δ⋆(G) is the source's statement (G connected has a spanning tree of maximum degree Δ⋆ ≤ n − 1)
--   - encoding: a deterministic algorithm (no machine model fixed) → one program of the CongruencyTU integer RAM (unit cost, no coin or query instruction), with one width constant fixed with the program bounding every register at every step by width·(1 + ⌊log₂(2 + scale)⌋) bits; reason: the paper fixes no machine; logarithmic words keep unit-cost arithmetic from trivializing running times; the external max-flow goal is stated on the same machine
--   - encoding: Ô(m) (subpolynomial factors in n hidden, footnote 8) → one program fixed first; ∀ ε > 0 ∃ K_ε > 0: cost ≤ K_ε·m·n^ε + K_ε; reason: the standard reading of n^{o(1)} factors with explicit constants
--   - encoding: given a feasible forest of G; compute augmenting chains → input [n, m, G's edge list, k, |E(F)|, F's edge list] in any order and orientation; output encMolecules lM ++ encFamily l𝓡 ++ encChains lA; reason: the output specifies the decomposition, its regions and the distinct node-sequence chains; it is not a new forest
--   - reading: 'compute Ω(f) many augmenting chains' (relative to an unnamed decomposition) → output the θ-molecular decomposition M (θ = ⌈10n/f⌉) and regions 𝓡 that the chains refer to, then a list of distinct chains, each augmenting w.r.t. (F, M, 𝓡), of length ≥ c·f with c > 0 universal; reason: an augmenting chain is only defined relative to (F, M, 𝓡); §16 builds them on θ = ⌈10n/f⌉; distinctness keeps 'many' from being met by repetition
--   - reading: f (number of components) → f ≥ 2; reason: standing assumption of §15 (the main subroutine runs only while f ≥ 2)
--   - reading: Definition 14.2 introduces θ in [1,n], but §16 sets θ = ⌈10n/f⌉ → the four decomposition clauses at θ = ⌈10n/f⌉ without imposing θ ≤ n; reason: the prescribed θ exceeds n when f < 10; the same clauses still apply and cover those source instances
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 40, Lemma 16.1

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_MinDegST_AddOne_Graph
import Definitions.Def_MinDegST_AddOne_Machine
import Definitions.Def_MinDegST_AddOne_Molecules

namespace MinDegST.AddOne

/-- **Lemma 16.1** (threshold form). One deterministic word-RAM program, a word-width constant and
a universal constant `c > 0`, fixed before `ε`, such that for every `ε > 0` there is `K_ε > 0` with:
for every connected simple graph `G` on `Fin n` (edge list `es`, `m = |es|`), every threshold
`k < n` for which `G` has a spanning tree of maximum degree `≤ k`, and every forest `F` of `G` of
maximum degree `≤ k + 1` with `f ≥ 2` components (edge list `fs`), on input `(es, k, fs)` the program
halts within `K_ε · m · n^ε + K_ε` steps and outputs a `θ`-molecular decomposition `M` of `F` for
`θ = ⌈10n/f⌉`, its reducible regions `𝓡`, and a list of at least `c · f` distinct augmenting chains
w.r.t. `(G, F, k, M, 𝓡)`. -/
theorem lemma_16_1 :
    ∃ (P : CongruencyTU.Program) (width : ℕ) (c : ℝ), Deterministic P ∧ 0 < c ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)) (k : ℕ)
        (F : SimpleGraph (Fin n)) (fs : List (Fin n × Fin n)),
        G.Connected → IsEdgeListOf G es → HasSpanningTreeLE G k → k < n →
        IsForestOf G F → Feasible k F → IsEdgeListOf F fs → 2 ≤ numComponents F →
          WordBounded P (encForestInput n es k fs) width (n + es.length)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)) (k : ℕ)
          (F : SimpleGraph (Fin n)) (fs : List (Fin n × Fin n)),
          G.Connected → IsEdgeListOf G es → HasSpanningTreeLE G k → k < n →
          IsForestOf G F → Feasible k F → IsEdgeListOf F fs → 2 ≤ numComponents F →
            HaltsWithin P (encForestInput n es k fs)
              (K * (es.length : ℝ) * (n : ℝ) ^ ε + K)
              (fun out => ∃ (lM : List (Molecule n)) (l𝓡 : List (List (Fin n)))
                  (lA : List (Chain n)),
                out = encMolecules lM ++ encFamily l𝓡 ++ encChains lA ∧
                lM.Nodup ∧
                IsThetaDecomp F k ⌈(10 * n : ℝ) / (numComponents F : ℝ)⌉₊ lM.toFinset ∧
                (∀ S ∈ l𝓡, S.Nodup) ∧ (l𝓡.map List.toFinset).Nodup ∧
                IsRegionsOf G F k lM.toFinset (l𝓡.map List.toFinset).toFinset ∧
                lA.Nodup ∧
                (∀ A ∈ lA, IsAugmentingChain G F k lM.toFinset (l𝓡.map List.toFinset).toFinset A) ∧
                c * (numComponents F : ℝ) ≤ (lA.length : ℝ)) := by sorry

end MinDegST.AddOne
