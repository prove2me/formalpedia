-- Prove2me | Theorems.Thm_LocalLemmaHierarchy_Completeness_memory_zero_lll
-- name    : LocalLemmaHierarchy.Completeness.memory_zero_lll
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T00:20:50.345727+00:00
-- url     : https://prove2.me/theorems/2adede72-010f-4ad8-88c8-e1c737dda2f3
-- title:
--   App. E.1, (E.5)–(E.6) — memory zero is the asymmetric Local Lemma
-- statement:
--   Let $G$ be a locally finite graph with neighbor orders, and $p_v\ge0$ vertex moduli. At memory zero there is one state per vertex (the one-site history $(v)$), and $x$ is a memory-zero certificate at moduli $p$ exactly when, for every $v$, $0\le x_v<1$ and
--   $$p_v\le x_v\prod_{u\in N_G(v)}(1-x_u),$$
--   i.e. $x_v\ge p_v\prod_{u\in N_G(v)}(1-x_u)^{-1}$ (E.5). Writing $x_v=r_v/(1+r_v)$ for $r_v>0$ turns this into $p_v\le\frac{r_v}{1+r_v}\prod_{u\in N_G(v)}\frac1{1+r_u}$ (E.6). These inequalities (with $p_v$ in place of $\lambda$) certify the polydisc with vertex moduli $p_v$: every finite region's independence polynomial is nonzero on $|z_v|\le p_v$.
--
--   Differences from the source:
--   - generalization: the sites form a countable set V → V is any type (no countability assumption); reason: no step of the proofs uses countability; the statement for countable V is the special case
--   - encoding: (E.5)–(E.6) at uniform λ, "more generally" with p_v in place of λ → stated directly at nonuniform vertex moduli p ≥ 0 (uniform λ is p = λ·1); reason: the text states the nonuniform version; the uniform one is its special case
--   - encoding: the memory-zero vector x on states → x : Hist → ℝ read at the one-site histories indState v; in (E.6) the vector s ↦ r(v(s))/(1 + r(v(s))); reason: the memory-zero states are exactly the one-site histories
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), App. E.1, (E.5)–(E.6), printed p. 31 (PDF p. 33); also §1.2, printed p. 3 (PDF p. 5)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory
import Definitions.Def_LocalLemmaHierarchy_Completeness_Graph

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness

/-- **App. E.1, (E.5)–(E.6): memory zero is the asymmetric Local Lemma**, printed p. 31 / PDF 33
(also §1.2, printed p. 3 / PDF 5). For the independent-set representation, the memory-zero system has
one state per vertex, and `x` is a memory-zero certificate at vertex moduli `p` exactly when
`0 ≤ x_v < 1` and `p_v ≤ x_v ∏_{u ∈ N(v)} (1 − x_u)` for every `v` (E.5); with `x_v = r_v/(1 + r_v)`,
`r_v > 0`, this is `p_v ≤ (r_v/(1 + r_v)) ∏_{u ∈ N(v)} 1/(1 + r_u)` (E.6); and these inequalities
certify the polydisc with vertex moduli `p_v` on every finite region. -/
theorem memory_zero_lll {V : Type} (G : SimpleGraph V) [G.LocallyFinite] (o : NeighborOrders G)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) :
    (∀ x : Hist (indRep G o) → ℝ, IsMemCertificate (indRep G o) 0 p x ↔
      ∀ v, 0 ≤ x (indState G o v) ∧ x (indState G o v) < 1 ∧
        p v ≤ x (indState G o v) * ∏ u ∈ G.neighborFinset v, (1 - x (indState G o u))) ∧
    (∀ r : V → ℝ, (∀ v, 0 < r v) →
      (IsMemCertificate (indRep G o) 0 p (fun s => r s.endpoint / (1 + r s.endpoint)) ↔
        ∀ v, p v ≤ r v / (1 + r v) * ∏ u ∈ G.neighborFinset v, 1 / (1 + r u))) ∧
    ∀ x : V → ℝ, (∀ v, 0 ≤ x v ∧ x v < 1) →
      (∀ v, p v ≤ x v * ∏ u ∈ G.neighborFinset v, (1 - x u)) →
      ∀ U : Finset V, ZeroFreeOn (indepPoly G) U p := by sorry

end LocalLemmaHierarchy.Completeness
