-- Prove2me | Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_1_1
-- name    : LocalLemmaHierarchy.Completeness.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:21:12.678108+00:00
-- url     : https://prove2.me/theorems/84086ceb-dd1f-471f-a8ac-d696d2095839
-- title:
--   Theorem 1.1 — a complete hierarchy of Local Lemmas: $\lambda_q\uparrow\lambda_c$ with gap $\le\min\{1/q,\pi^2/(q+1)^2\}$
-- statement:
--   For every locally finite graph $G$ with fixed neighbor orders, $\lambda_0\le\lambda_1\le\cdots\uparrow\lambda_c$. Memory zero is the asymmetric Local Lemma, and for every $q\ge1$,
--   $$0\le\lambda_c(G)-\lambda_q(G)\le\min\Bigl\{\frac1q,\frac{\pi^2}{(q+1)^2}\Bigr\}.\qquad(1.5)$$
--   The order $q^{-2}$ cannot be improved uniformly over graphs. Every certificate is also valid for arbitrary, nonuniform moduli when $p$ in each row is replaced by the modulus at its endpoint.
--
--   Here $\lambda_c(G)$ is the uniform Shearer threshold (1.1) and $\lambda_q(G)$ the memory-$q$ threshold of the independent-set representation. Concretely the statement asserts, for a graph with a vertex: (1) $q\mapsto\lambda_q$ is nondecreasing, bounded by $\lambda_c$, and converges to $\lambda_c$; (2) a vector on the memory-zero states is a certificate at vertex moduli $p\ge0$ iff $0\le x_v<1$ and $p_v\le x_v\prod_{u\in N(v)}(1-x_u)$ for all $v$, and $\lambda_0=\sup\{t\ge0:\exists x\in[0,1)^V,\ t\le x_v\prod_{u\in N(v)}(1-x_u)\ \forall v\}$; (3) for $q\ge1$, $\lambda_q\le\lambda_c\le\lambda_q+\min\{1/q,\pi^2/(q+1)^2\}$; (4) for every $q\ge1$ and any neighbor orders on $C_{q+3}$, $\lambda_c(C_{q+3})-\lambda_q(C_{q+3})\ge\pi^2/(16(q+3)^2)$ (the example named right after the theorem); (5) every memory-$q$ certificate at nonuniform vertex moduli $p\ge0$ makes the independence polynomial of every finite region nonzero on $|z_v|\le p_v$ and gives Shearer's condition $Z_{G[U]}(-p)>0$ for every finite $U$.
--
--   Differences from the source:
--   - encoding: a locally finite graph (Corollary E.1: "a graph with a vertex") → [Nonempty V]; reason: for V = ∅ both thresholds are +∞ and the gap λ_c − λ_q is undefined; the hypothesis only excludes that case
--   - generalization: the sites form a countable set V → V is any type (no countability assumption); reason: no step of the proofs uses countability; the statement for countable V is the special case
--   - encoding: fixed neighbor orders → NeighborOrders G: ranks injective on each N(v); reason: every total order on the finite set N(v) is induced by such a rank, and only comparisons are used
--   - encoding: real thresholds λ_c, λ_q and the gap 0 ≤ λ_c − λ_q ≤ min{…} → ℝ≥0∞-valued shearerThreshold and lambdaQ; λ_q ≤ λ_c ∧ λ_c ≤ λ_q + ENNReal.ofReal (min …); reason: avoids truncated subtraction; for a graph with a vertex both values are finite (≤ 1) and the two forms agree
--   - encoding: "Memory zero is the asymmetric Local Lemma" → a memory-zero certificate at moduli p is exactly an x ∈ [0,1)^V with p_v ≤ x_v ∏_{u∈N(v)} (1 − x_u), and λ_0 is the supremum of the uniform t these inequalities admit; reason: the identification of App. E.1 (E.5)–(E.6) and §1.2
--   - generalization: "The order q^{−2} cannot be improved uniformly over graphs" → for every q ≥ 1 and every neighbor orders on C_{q+3}: λ_q(C_{q+3}) + π²/(16(q+3)²) ≤ λ_c(C_{q+3}); reason: this is the uniform lower-bound example the paper names after the theorem (Prop. 3.10); since (q+3)² ≤ 4(q+1)² for q ≥ 1 it gives gap ≥ (π²/64)/(q+1)² for every q, so no o(q^{−2}) bound holds for all graphs
--   - encoding: "Every certificate is also valid for arbitrary, nonuniform moduli" → every memory-q certificate at vertex moduli p ≥ 0 gives, for every finite U, zero-freeness of Ind_{G[U]} on |z_v| ≤ p_v and Ind_{G[U]}(−p) > 0; reason: validity means certifying the polydisc on every finite region (Theorem 3.2), equivalently Shearer’s condition (Theorem 2.3)
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Theorem 1.1, printed p. 4 (PDF p. 6), with the sentence following it; proof App. E.3, printed p. 33 (PDF p. 35)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory
import Definitions.Def_LocalLemmaHierarchy_Completeness_Graph

open scoped ENNReal NNReal
open Filter Topology

namespace LocalLemmaHierarchy.Completeness

/-- **Theorem 1.1 (A complete hierarchy of Local Lemmas)**, printed p. 4 / PDF 6 (proof App. E.3,
printed 33 / PDF 35). For every locally finite graph `G` (with a vertex) and fixed neighbor orders:
(1) `λ_0 ≤ λ_1 ≤ ⋯ ↑ λ_c`; (2) memory zero is the asymmetric Local Lemma; (3) for every `q ≥ 1`,
`0 ≤ λ_c(G) − λ_q(G) ≤ min{1/q, π²/(q+1)²}` (1.5); (4) the order `q^{−2}` cannot be improved
uniformly over graphs: for every `q ≥ 1` and any neighbor orders, `C_{q+3}` has
`λ_c − λ_q ≥ π²/(16(q+3)²)`; (5) every memory-`q` certificate at nonuniform vertex moduli `p` (the
row at a state using the modulus at its endpoint) certifies zero-freeness on the polydisc
`|z_v| ≤ p_v`, and Shearer's condition, on every finite region. -/
theorem theorem_1_1 {V : Type} [Nonempty V] (G : SimpleGraph V) [G.LocallyFinite]
    (o : NeighborOrders G) :
    (Monotone (lambdaQ G o) ∧ (∀ q, lambdaQ G o q ≤ shearerThreshold G) ∧
      Tendsto (lambdaQ G o) atTop (𝓝 (shearerThreshold G))) ∧
    ((∀ p : V → ℝ, (∀ v, 0 ≤ p v) → ∀ x : Hist (indRep G o) → ℝ,
        (IsMemCertificate (indRep G o) 0 p x ↔
          ∀ v, 0 ≤ x (indState G o v) ∧ x (indState G o v) < 1 ∧
            p v ≤ x (indState G o v) * ∏ u ∈ G.neighborFinset v, (1 - x (indState G o u)))) ∧
      lambdaQ G o 0 =
        ⨆ (t : ℝ≥0) (_ : ∃ x : V → ℝ, ∀ v, 0 ≤ x v ∧ x v < 1 ∧
            (t : ℝ) ≤ x v * ∏ u ∈ G.neighborFinset v, (1 - x u)), (t : ℝ≥0∞)) ∧
    (∀ q : ℕ, 1 ≤ q →
      lambdaQ G o q ≤ shearerThreshold G ∧
      shearerThreshold G ≤
        lambdaQ G o q + ENNReal.ofReal (min (1 / (q : ℝ)) (Real.pi ^ 2 / ((q : ℝ) + 1) ^ 2))) ∧
    (∀ q : ℕ, 1 ≤ q → ∀ o' : NeighborOrders (SimpleGraph.cycleGraph (q + 3)),
      lambdaQ (SimpleGraph.cycleGraph (q + 3)) o' q +
          ENNReal.ofReal (Real.pi ^ 2 / (16 * ((q : ℝ) + 3) ^ 2)) ≤
        shearerThreshold (SimpleGraph.cycleGraph (q + 3))) ∧
    (∀ (q : ℕ) (p : V → ℝ), (∀ v, 0 ≤ p v) → ∀ x : Hist (indRep G o) → ℝ,
      IsMemCertificate (indRep G o) q p x → ∀ U : Finset V,
        ZeroFreeOn (indepPoly G) U p ∧
        0 < MvPolynomial.eval (fun v => -p v) (indepPoly G U)) := by sorry

end LocalLemmaHierarchy.Completeness
