-- Prove2me | Theorems.Thm_MaxCompForest_theorem_3_1
-- name    : MaxCompForest.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:16.801496+00:00
-- url     : https://prove2.me/theorems/e6df2c3c-af04-4616-90c0-308f090bf581
-- title:
--   Theorem 3.1 — approximation from few slow vertex modes: $(1+\varepsilon)$-approximate maximum-completion forests in $(Ckq/(\gamma\varepsilon))^{O(k)}\mathrm{poly}(L)$ bit time
-- statement:
--   There are one deterministic machine and absolute constants $C,a,b$ with the following property. Let $G$ be a connected simple graph with positive rational conductances, $q$ an integer with $1\le q<|V(G)|$, $\gamma$ a rational with $0<\gamma\le1$ and $\lambda_{q+1}(N_G)\ge\gamma$, $\varepsilon$ a rational with $0<\varepsilon\le1$, and $0\le k\le|V(G)|-1$ an integer. On this input, of total binary length $L$, the machine returns $k$ distinct original edges forming a forest $F$, together with its exact rational score $P_{T\sim\mathrm{WST}(G)}(F\subseteq T)=\Phi_G(F)/\tau_c(G)$, such that
--   $$
--   P_{T\sim\mathrm{WST}(G)}(F\subseteq T)\ge\frac{1}{1+\varepsilon}\max_{\substack{J\subseteq E(G)\\|J|=k}}P_{T\sim\mathrm{WST}(G)}(J\subseteq T),
--   $$
--   within
--   $$
--   \Big(\frac{Ckq}{\gamma\varepsilon}\Big)^{ak}(L+2)^{b}
--   $$
--   steps. For $k=0$ the empty set is returned. All original edges are selectable, and no conductance-ratio bound, supplied partition or eigenvector oracle is required. The case $q=1$ is a global-gap assumption; for $q\ge2$ the lower nonconstant eigenvalues may be arbitrarily small.
--
--   Here $\Phi_G(F)=\sum_{T\supseteq F}c(T)$ and $T$ is sampled with probability proportional to the product of its conductances. Exact selection is W[1]-hard on this class, and brute force costs $m^k$, which meets a bound of this shape only if $b$ may depend on $k$: the absolute exponent on $L$ is the content of the theorem.
--
--   Differences from the source:
--   - reading: “a deterministic algorithm … bit time” → one Mathlib multi-stack machine `TM2ComputableAux Sym Sym` on a fixed binary encoding; reason: the paper names no machine; a bit-operation algorithm and a multi-stack machine differ by a polynomial, which the time bound absorbs with changed absolute constants
--   - reading: “All algorithmic inputs are binary rational” → arbitrary rationals written in binary as reduced numerator and denominator; reason: Theorem 3.1 says “positive rational”; dyadic-only inputs would be the weaker reading
--   - reading: the theorem's sentence returns the edges → the output word also carries the exact rational score $P(F\subseteq T)=\Phi_G(F)/\tau_c(G)$; reason: “Our deterministic schemes return a forest of labelled original edges together with its exact rational score”, pp.14–15, and p.3; the score of a forest is defined on p.1 as “For a forest F, the score is P(F ⊆ T)”
--   - generalization: (3.4) is stated for $k\ge1$; for $k=0$ “the empty set is returned exactly” → at $k=0$ the same formula gives the time bound $(L+2)^b$; reason: the printed clause for $k\ge1$ is unchanged, and a machine that reads $k$ decides this case in polynomial time
--   - encoding: the max over $J$ in (3.3), with the factor $1/(1+\varepsilon)$ → $P(J\subseteq T)\le(1+\varepsilon)P(F\subseteq T)$ for every $k$-subset $J$; reason: the same statement over a finite family; the division is cleared
--   - encoding: the algorithm is run under the theorem's hypotheses → behaviour outside the hypotheses is unconstrained, including non-halting; reason: the theorem assumes the promise; the machine is not asked to verify it
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem 3.1, p.15; conventions pp.14–15

import Mathlib
import Definitions.Def_MaxCompForest_RInst
import Definitions.Def_MaxCompForest_lam
import Definitions.Def_MaxCompForest_deg
import Definitions.Def_MaxCompForest_IsForest
import Definitions.Def_MaxCompForest_inclProb
import Definitions.Def_MaxCompForest_timeBound
import Definitions.Def_MaxCompForest_encIn
import Definitions.Def_MaxCompForest_encOut
import Definitions.Def_CFLOutliers_OutputsWithin
import Definitions.Def_OnlineCRS_Combine_Sym
open EffResSparsify.ResistanceSketch
open OnlineCRS.Combine (Sym)
open CFLOutliers (OutputsWithin)

namespace MaxCompForest

/-- **Theorem 3.1 (Approximation from few slow vertex modes).** One machine and absolute `C`, `a`, `b`, chosen before
every instance; `q`, `γ`, `ε`, `k` are read from the input. The promise `λ_{q+1}(N_G) ≥ γ` is a hypothesis, and no
bound on `λ₂` or on the conductance ratio is assumed.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.15; the exact rational score is the standing convention of pp.14–15, and the score of a forest is
`P(F ⊆ T) = Φ_G(F)/τ_c(G)` (p.1: "For a forest F, the score is P(F ⊆ T)").

**Formalization Note.** The max over `J` in (3.3) is a bound against each `k`-subset `J`, cyclic ones included (their
probability is `0`); the division is cleared. At `k = 0` the time bound is `(L + 2)^b`. -/
theorem theorem_3_1 :
    ∃ (M : Turing.TM2ComputableAux Sym Sym) (C a b : ℕ), 0 < C ∧
      ∀ (I : RInst) (q k : ℕ) (γ ε : ℚ),
        I.graph.IsConnected → I.graph.IsSimple → 1 ≤ q → q < I.n → 0 < γ → γ ≤ 1 →
        (γ : ℝ) ≤ lam I.graph (deg I.graph) q → 0 < ε → ε ≤ 1 → k + 1 ≤ I.n →
        ∃ (F : List (Fin I.m)) (score : ℚ),
          F.Nodup ∧ F.length = k ∧ IsForest I.graph F.toFinset ∧
          (score : ℝ) = inclProb I.graph F.toFinset ∧
          (k = 0 → F = []) ∧
          (∀ J : Finset (Fin I.m), J.card = k →
            inclProb I.graph J ≤ (1 + (ε : ℝ)) * inclProb I.graph F.toFinset) ∧
          OutputsWithin M (encIn I q γ ε k) (encOut F score)
            (timeBound C a b k q γ ε (encIn I q γ ε k).length) := by sorry

end MaxCompForest
