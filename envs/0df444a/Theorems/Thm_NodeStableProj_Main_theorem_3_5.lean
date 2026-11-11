-- Prove2me | Theorems.Thm_NodeStableProj_Main_theorem_3_5
-- name    : NodeStableProj.Main.theorem_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:59:25.577996+00:00
-- url     : https://prove2.me/theorems/a6a5bf02-754e-4be3-953a-96d4cf7939bb
-- title:
--   Theorem 3.5 — a node-stable projection with a private input size releasing (P(G), D̂(G)) in time O(m log(n/δ))
-- statement:
--   There is one randomized program `adapt-P` on the machine which, given an encoded graph $G$ (vertex labels in $\mathbb N$, any order of vertices and edges), a degree bound $D\in\mathbb N$, $D\ge1$, and stability parameters $\varepsilon,\delta\in(0,1)$, outputs a pair $(\mathcal P(G),\hat D(G))$ of a graph on $V(G)$ and a released degree bound, such that, with $n=|V(G)|$ and $m=|E(G)|$:
--   1. the output law is a probability law (the output map is measurable), and almost surely the run halts and $D<\hat D$, $\mathcal P(G)$ is a $\hat D$-bounded subgraph of $G$ on $V(G)$, $\mathcal P(G)=G$ if $G$ is $D$-bounded, and every edge of $G$ omitted from $\mathcal P(G)$ has an endpoint of degree at least $D$ in $\mathcal P(G)$ — so, conditioned on any value $\hat D$, the first output is a $(D,\hat D)$-projection;
--   2. for every $G'$ obtained from $G$ by adding a node $v^*$ with arbitrary incident edges, and all encodings of $G$ and $G'$,
--   $$(\mathcal P(G),\hat D(G))\ \approx_{\varepsilon,\delta}\ (\mathcal P(G')_{-v^*},\hat D(G'));$$
--   3. for every $c>0$ there is $C$ such that if $n\ge2$, $\delta\le1/2$ and $\varepsilon\ge c/n$, then almost surely
--   $$\hat D(G)\le D+C\big(\lambda_n\sqrt D+\lambda_n^2\big),\qquad \lambda_n=\frac{\log(n/\delta)\sqrt{\ln(1/\delta)}}{\varepsilon};$$
--   4. for all $c,c'>0$ there is $C$ such that if $n,m\ge2$, $n\le c'm$, $\delta\le1/2$ and $\varepsilon\ge c/n$, then every run halts within $C\,m\log(n/\delta)$ steps.
--
--   This is the paper's formal headline: a near-linear-time projection onto bounded-degree graphs that is distributionally node-stable without assuming the number of vertices is public.
--
--   Differences from the source:
--   - reading: "There is a randomized algorithm adapt-P_{D,ε,δ} … can be implemented in time" → one Admissible program on the machine, taking D, ε, δ and an encoding of G as input, with output law the pushforward of the uniform tape; items 1–3 for every encoding, item 4 for every tape and every encoding; reason: the paper names no machine; the program is fixed before the parameters
--   - reading: D ∈ N → D ≥ 1; reason: Definition 3.1 defines (D, D̂)-projections only for 0 < D
--   - reading: "Conditioned on any possible value D̂ of the second output, P is a (D, D̂)-projection" → almost surely the run halts and the realized pair satisfies D < D̂, E(P(G)) ⊆ E(G), P(G) D̂-bounded, P(G) = G on G_D, and Equation (1); reason: conditioning on every possible value is the almost-sure statement on the pair
--   - reading: "ε = Ω(1/n)", "O(·)", "n = O(m)", asymptotic bounds → ∀ c > 0 (and c' > 0) ∃ C: ε ≥ c/n (and n ≤ c'm) imply the bound with constant C; n, m ≥ 2; reason: §2 conventions; App. C uses ε ≥ c/n
--   - encoding: outputs (P(G), D̂(G)) and P(G')_{−v*} → the decoded (edge set, ℕ) in Option (none if the run does not halt), with the discrete σ-algebra; edges at v* deleted from the G' output; reason: the output graph is on V(G); comparing edge sets compares the graphs
--   - encoding: the output (P(G), D̂(G)) is a random variable → item 1 also states that the output law is a probability measure; reason: implied by the source (a law of an output); rules out the zero junk value of a pushforward under a non-measurable map
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 12, Theorem 3.5 (proof: Appendix C, pp. 33–34)

import Mathlib
import Definitions.Def_PFRelease_Indist
import Definitions.Def_NodeStableProj_Main_Graph
import Definitions.Def_NodeStableProj_Main_Machine

open MeasureTheory

namespace NodeStableProj.Main

/-- Theorem 3.5 (Stable projection with a private input size), p. 12: one program on the machine,
taking `D`, `ε`, `δ` and an encoded graph `G`, releasing `(P(G), D̂(G))`, such that
(1) the output law is a probability law and almost surely the run halts, `D < D̂`, `P(G)` is a `D̂`-bounded subgraph of `G` on `V(G)`,
`P(G) = G` if `G` is `D`-bounded, and every omitted edge has an endpoint of `P(G)`-degree `≥ D`;
(2) for `G'` obtained from `G` by adding `v*` with arbitrary edges,
`(P(G), D̂(G)) ≈_{ε,δ} (P(G')_{−v*}, D̂(G'))`;
(3) for every `c > 0` there is `C` with: `n ≥ 2`, `δ ≤ 1/2`, `ε ≥ c/n` imply, almost surely,
`D̂ ≤ D + C(λ_n √D + λ_n²)`, `λ_n = log(n/δ) √(ln(1/δ))/ε`;
(4) for all `c, c' > 0` there is `C` with: `n, m ≥ 2`, `n ≤ c' m`, `δ ≤ 1/2`, `ε ≥ c/n` imply
that every run halts within `C m log(n/δ)` steps. -/
theorem theorem_3_5 :
    ∃ P : Program, Admissible P ∧
      (∀ (D : ℕ) (ε δ : ℝ) (G : Graph) (vs : List ℕ) (es : List (ℕ × ℕ)),
        1 ≤ D → 0 < ε → ε < 1 → 0 < δ → δ < 1 → IsEncoding G vs es →
        IsProbabilityMeasure (releaseProgramLaw P D ε δ vs es) ∧
        ∀ᵐ o ∂(releaseProgramLaw P D ε δ vs es), ∃ (E : Finset (Sym2 ℕ)) (Dhat : ℕ),
          o = some (E, Dhat) ∧ D < Dhat ∧ E ⊆ G.E ∧ (G.withEdges E).Bounded Dhat ∧
          (G.Bounded D → E = G.E) ∧ G.EdgePreserving D (G.withEdges E)) ∧
      (∀ (D : ℕ) (ε δ : ℝ) (G G' : Graph) (vstar : ℕ) (vs vs' : List ℕ)
        (es es' : List (ℕ × ℕ)),
        1 ≤ D → 0 < ε → ε < 1 → 0 < δ → δ < 1 → AddsNode G G' vstar →
        IsEncoding G vs es → IsEncoding G' vs' es' →
        PFRelease.Indist (releaseProgramLaw P D ε δ vs es)
          ((releaseProgramLaw P D ε δ vs' es').map (releaseDeleteVertex vstar))
          ε δ) ∧
      (∀ c : ℝ, 0 < c → ∃ C : ℝ, ∀ (D : ℕ) (ε δ : ℝ) (G : Graph) (vs : List ℕ)
        (es : List (ℕ × ℕ)),
        1 ≤ D → 0 < ε → ε < 1 → 0 < δ → δ < 1 → IsEncoding G vs es →
        2 ≤ G.V.card → δ ≤ 1 / 2 → c / G.V.card ≤ ε →
        ∀ᵐ o ∂(releaseProgramLaw P D ε δ vs es), ∃ (E : Finset (Sym2 ℕ)) (Dhat : ℕ),
          o = some (E, Dhat) ∧
          (Dhat : ℝ) ≤ D + C * (Real.log (G.V.card / δ) * Real.sqrt (Real.log (1 / δ)) / ε *
              Real.sqrt D + (Real.log (G.V.card / δ) * Real.sqrt (Real.log (1 / δ)) / ε) ^ 2)) ∧
      (∀ c c' : ℝ, 0 < c → 0 < c' → ∃ C : ℝ, ∀ (D : ℕ) (ε δ : ℝ) (G : Graph) (vs : List ℕ)
        (es : List (ℕ × ℕ)),
        1 ≤ D → 0 < ε → ε < 1 → 0 < δ → δ < 1 → IsEncoding G vs es →
        2 ≤ G.V.card → 2 ≤ G.E.card → (G.V.card : ℝ) ≤ c' * G.E.card →
        δ ≤ 1 / 2 → c / G.V.card ≤ ε →
        HaltsWithin P (releaseInit D ε δ vs es)
          (C * G.E.card * Real.log (G.V.card / δ))) := by sorry

end NodeStableProj.Main
