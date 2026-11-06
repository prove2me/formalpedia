-- Prove2me | Theorems.Thm_KMPMixing_lemma_4_10
-- name    : KMPMixing.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:11:46.984351+00:00
-- url     : https://prove2.me/theorems/97b3b57d-0d02-4086-b934-d363e1f14907
-- title:
--   Lemma 4.10 — exact coupling of two KMP chains along a connected edge sequence
-- statement:
--   Let $d\ge3$ and $t>d^{1000}$. Let $e_1,\dots,e_N$ be edges on the vertex set $[d]$ such that the graph $([d],\{e_1,\dots,e_N\})$ is connected. Let $(X^{(0)},\widetilde X^{(0)})$ be random vectors in $\Delta_G$ with any joint law $q_0$ such that $\widetilde X^{(0)}\sim\mathrm{Unif}(\Delta_G)$, and let
--   $$
--   \eta=\Pr\big[\|X^{(0)}-\widetilde X^{(0)}\|_1>t\,d^{-19}\big].
--   $$
--   Then there is a coupling of two processes $(X^{(s)})_{s=0}^N$ and $(\widetilde X^{(s)})_{s=0}^N$ with initial joint law $q_0$, each applying the redistribution rule of Definition 3.1 to the edge $e_s$ at step $s$, such that
--   $$
--   \Pr\big[X^{(N)}\ne\widetilde X^{(N)}\big]\le\eta+\frac1{d^2}.
--   $$
--
--   This is the second stage of the two-stage coupling: once the profiles are close, a connected sequence of shared edges merges them exactly.
--
--   Differences from the source:
--   - reading: a coupling of two processes with the given initial joint distribution, each following the fixed-edge rule → a probability $Q$ on pairs of paths in $\Delta_G^{N+1}$ whose time-$0$ pair has law $q_0$ and whose two path marginals are the chains started from the marginals of $q_0$ with kernels $K_{e_1},\dots,K_{e_N}$; reason: this is the standard meaning of a coupling of two processes; the step-wise (Markovian) coupling of the proof is one such $Q$
--   - encoding: the connected graph $G=(V=[d],E)$ of the statement → not a parameter; reason: $G$ enters only through $\Delta_G$, which depends on $d$ and $t$ alone, and the $e_s$ need not be edges of $G$
--   - encoding: edges $e_s$ on $[d]$ → pairs $(i_s,j_s)$ with $i_s\ne j_s$, connectivity of the graph with edge set $\{\{i_s,j_s\}\}$; reason: same edges
-- source:
--   Chen et al., arXiv:2609.38044, Lemma 4.10, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_KMPMixing_kmpChain
open MarkovMixing

namespace KMPMixing

/-- **Lemma 4.10** (arXiv:2609.38044, p.25 (PDF p.27)). Let `d ≥ 3` and `t > d^{1000}`. Fix
edges `e_1, …, e_N` on the vertex set `[d]` such that the graph `([d], {e_1, …, e_N})` is
connected. Let `X^{(0)}, X̃^{(0)}` be random vectors in `Δ_G` with an arbitrary joint law `q₀` such
that `X̃^{(0)} ∼ Unif(Δ_G)`, and let `η = Pr[‖X^{(0)} − X̃^{(0)}‖₁ > t·d^{−19}]`. Then there is a
coupling of two processes `(X^{(s)})_{s=0}^N` and `(X̃^{(s)})_{s=0}^N` with the given initial joint
law, each applying the redistribution rule of Definition 3.1 to the edge `e_s` at step `s`, such
that `Pr[X^{(N)} ≠ X̃^{(N)}] ≤ η + 1/d²`.

**Formalization Note** A coupling of the two processes is a probability `Q` on pairs of paths
`(ω, ω̃) ∈ Δ^{N+1} × Δ^{N+1}` (paths indexed by `Fin (N+1)`) such that the law of
`(ω₀, ω̃₀)` is `q₀`, and each path, on its own, has the law of the chain started from the
corresponding marginal of `q₀` and moved at step `s` by the fixed-edge kernel
`edgeKernel i_s j_s` (Definition 3.1, step 2). Edges are pairs `(i_s, j_s)` with `i_s ≠ j_s`.
`‖r − r̃‖₁ = Σ_v |r_v − r̃_v|`. The graph `G` of the statement enters only through `Δ_G`, which
depends on `d` and `t` alone, so it is not a parameter. -/
theorem lemma_4_10 {d t N : ℕ} (hd : 3 ≤ d) (ht : d ^ 1000 < t)
    (es : Fin N → Fin d × Fin d) (hne : ∀ s, (es s).1 ≠ (es s).2)
    (hconn : (SimpleGraph.fromEdgeSet (Set.range fun s => s((es s).1, (es s).2))).Connected)
    (q₀ : State d t × State d t → ℝ) (hq₀ : IsDist q₀)
    (hunif : ∀ b : State d t, ∑ a : State d t, q₀ (a, b) = uniformDist (State d t) b) :
    ∃ Q : (Fin (N + 1) → State d t) × (Fin (N + 1) → State d t) → ℝ,
      IsDist Q ∧
      (∀ a b : State d t,
        ∑ ω ∈ Finset.univ.filter (fun ω : (Fin (N + 1) → State d t) × (Fin (N + 1) → State d t) =>
            ω.1 0 = a ∧ ω.2 0 = b), Q ω = q₀ (a, b)) ∧
      (∀ ω : Fin (N + 1) → State d t,
        ∑ ω' : Fin (N + 1) → State d t, Q (ω, ω') =
          (∑ b : State d t, q₀ (ω 0, b)) *
            ∏ s : Fin N, edgeKernel (es s).1 (es s).2 (ω s.castSucc) (ω s.succ)) ∧
      (∀ ω' : Fin (N + 1) → State d t,
        ∑ ω : Fin (N + 1) → State d t, Q (ω, ω') =
          (∑ a : State d t, q₀ (a, ω' 0)) *
            ∏ s : Fin N, edgeKernel (es s).1 (es s).2 (ω' s.castSucc) (ω' s.succ)) ∧
      ∑ ω ∈ Finset.univ.filter (fun ω : (Fin (N + 1) → State d t) × (Fin (N + 1) → State d t) =>
          ω.1 (Fin.last N) ≠ ω.2 (Fin.last N)), Q ω ≤
        (∑ p ∈ Finset.univ.filter (fun p : State d t × State d t =>
            (t : ℝ) * (d : ℝ) ^ (-19 : ℤ) <
              ∑ v : Fin d, |((p.1.1 v : ℕ) : ℝ) - ((p.2.1 v : ℕ) : ℝ)|), q₀ p) +
          1 / (d : ℝ) ^ 2 := by sorry

end KMPMixing
