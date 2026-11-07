-- Prove2me | Theorems.Thm_OnlineCAP_proposition_3_5
-- name    : OnlineCAP.proposition_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:30.2497+00:00
-- url     : https://prove2.me/theorems/72c36355-8631-43b1-8d3d-f14fe1f81259
-- title:
--   Proposition 3.5 (= Theorem 1.7) — an α-competitive algorithm on cycles gives one on general graphs, weighted and unweighted
-- statement:
--   Fix $n$, a ratio $\alpha\in\mathbb R$, and whether algorithms are required to be deterministic.
--
--   1. **Unweighted.** Suppose that for every link set $L\subseteq\binom V2$ on the cycle $v_0v_1\cdots v_{n-1}v_0$, OCycAP with cut arrivals (unit costs) has an $\alpha$-competitive algorithm. Then for every $k\ge1$, every $k$-edge-connected multigraph $G$ on $V=\{v_0,\dots,v_{n-1}\}$ and every link set $L\subseteq\binom V2$, OCAP with cut arrivals on $(G,L)$ has an $\alpha$-competitive algorithm.
--   2. **Weighted.** The same with arbitrary nonnegative link costs on both sides (OWCycAP → OWCAP).
--
--   "$\alpha$-competitive" means competitive in expectation against an oblivious adversary; in the deterministic case both algorithms are deterministic. Theorem 1.7 (p.4) states the same two transfers.
--
--   **Formalization Note** The deterministic case is the flag `det`. The proof uses the circumference disposition theorem of Dinitz–Karzanov–Lomonosov (Theorem 3.4), which is not a hypothesis here.
--
--   Differences from the source:
--   - generalization: a constant ratio α for all cycles → the number of vertices n and the ratio α fixed, the hypothesis only about cycles on n vertices; reason: the source's statement (all n, one α) follows by applying it for each n; it also gives the transfer for any ratio function α(n)
--   - generalization: a k-edge-connected graph → a k-edge-connected finite multigraph (parallel edges and loops allowed); reason: simple graphs are a special case; edge-connectivity augmentation is routinely posed for multigraphs
--   - reading: k-edge-connected (k unrestricted) → k ≥ 1; reason: Theorem 3.4, used in the proof, is for connected graphs; for k = 0 a disconnected graph's 0-cuts are unions of components, not arcs of a cycle, and augmentation of a 0-edge-connected graph is not what the paper treats
--   - reading: α-competitive algorithm → both randomized (in expectation, oblivious adversary) and deterministic, the transfer preserving determinism; reason: §2.2 defines both and the paper uses both (Theorems 1.3, 1.4); the strongest reading
--   - encoding: OCAP with cut-arrivals on a cycle → the standard labelled cycle on Fin n with k = 2; reason: every cycle on the vertex set is a relabelling of it and relabelling preserves competitive ratios
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Proposition 3.5, p.13; Theorem 1.7, p.4

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg
import Definitions.Def_OnlineCAP_OnlineHSInstance
import Definitions.Def_OnlineCAP_OnlineHSInstance_OPT
import Definitions.Def_OnlineCAP_IsCompetitive
import Definitions.Def_OnlineCAP_crosses
import Definitions.Def_OnlineCAP_edgeCut
import Definitions.Def_OnlineCAP_IsKCut
import Definitions.Def_OnlineCAP_capInstance
import Definitions.Def_OnlineCAP_cycleEnds
import Definitions.Def_OnlineCAP_cycleInstance
import Definitions.Def_OnlineCAP_IsKEdgeConnected
import Definitions.Def_OnlineCAP_RandOnlineAlg_IsDeterministic

open MeasureTheory Filter Asymptotics

namespace OnlineCAP

/-- **Proposition 3.5 (from cycles to general graphs) = Theorem 1.7.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Proposition 3.5,
p.13 (PDF p.13): "If there is an α-competitive algorithm A for OCAP with cut-arrivals on a cycle,
then there is an α-competitive algorithm for OCAP with cut-arrivals on a general graph. This holds
in the weighted case as well." Theorem 1.7, p.4, states the same for OCycAP → OCAP and
OWCycAP → OWCAP.

Fix the number of vertices `n`, a ratio `α`, and whether algorithms must be deterministic
(`det`).
1. (Unweighted.) If for every link set `L` on the cycle `v₀ ⋯ v_{n−1} v₀` OCycAP with unit costs has
   an `α`-competitive algorithm, then for every `k ≥ 1`, every k-edge-connected multigraph on the
   `n` vertices and every link set `L`, OCAP with unit costs has one.
2. (Weighted.) The same with arbitrary nonnegative costs on both sides.

**Formalization Note.** "α-competitive" is competitiveness in expectation against an oblivious
adversary (§2.2); with `det = true` both algorithms are deterministic. The ratio is fixed per `n`,
which gives the statement for a constant ratio and for any ratio function `α(n)`. The cycle of the
hypothesis is the standard labelled cycle; every cycle on the vertex set is a relabelling of it. -/
theorem proposition_3_5 (n : ℕ) (α : ℝ) (det : Bool) :
    ((∀ L : Finset (Sym2 (Fin n)), (∀ ℓ ∈ L, ¬ ℓ.IsDiag) →
        ∃ A : RandOnlineAlg (Sym2 (Fin n)) (Finset (Fin n)), (det = true → A.IsDeterministic) ∧
          IsCompetitive (cycleInstance n L (fun _ => 1)) A α) →
      ∀ k : ℕ, 1 ≤ k → ∀ (E : Type) [Fintype E] (ends : E → Sym2 (Fin n)),
        IsKEdgeConnected ends k → ∀ L : Finset (Sym2 (Fin n)), (∀ ℓ ∈ L, ¬ ℓ.IsDiag) →
          ∃ A : RandOnlineAlg (Sym2 (Fin n)) (Finset (Fin n)), (det = true → A.IsDeterministic) ∧
            IsCompetitive (capInstance ends k L (fun _ => 1)) A α) ∧
    ((∀ L : Finset (Sym2 (Fin n)), (∀ ℓ ∈ L, ¬ ℓ.IsDiag) →
        ∀ c : Sym2 (Fin n) → ℝ, (∀ ℓ ∈ L, 0 ≤ c ℓ) →
          ∃ A : RandOnlineAlg (Sym2 (Fin n)) (Finset (Fin n)), (det = true → A.IsDeterministic) ∧
            IsCompetitive (cycleInstance n L c) A α) →
      ∀ k : ℕ, 1 ≤ k → ∀ (E : Type) [Fintype E] (ends : E → Sym2 (Fin n)),
        IsKEdgeConnected ends k → ∀ L : Finset (Sym2 (Fin n)), (∀ ℓ ∈ L, ¬ ℓ.IsDiag) →
          ∀ c : Sym2 (Fin n) → ℝ, (∀ ℓ ∈ L, 0 ≤ c ℓ) →
            ∃ A : RandOnlineAlg (Sym2 (Fin n)) (Finset (Fin n)),
              (det = true → A.IsDeterministic) ∧ IsCompetitive (capInstance ends k L c) A α) := by sorry

end OnlineCAP
