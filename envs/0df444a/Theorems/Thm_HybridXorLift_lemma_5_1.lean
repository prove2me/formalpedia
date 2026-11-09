-- Prove2me | Theorems.Thm_HybridXorLift_lemma_5_1
-- name    : HybridXorLift.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:23:22.614569+00:00
-- url     : https://prove2.me/theorems/edf96e42-0105-4f2d-ad89-3182b08cf39d
-- title:
--   Lemma 5.1 — telescoping: $P'_z(h_m) = \ell^{\xi_m}_{h_m}\prod_t \ell^{\xi_t}_{h_t}/\ell^{\xi_{t+1}}_{h_t}$ and $P'_z(h_m) \ge (1+\eta)^{-(n+1)}\ell_{h_m}(z)$
-- statement:
--   Throughout, $n \ge 1$, $r \ge 1$, $q \ge 1$ are integers and $A$ is a parallel $q$-query hybrid algorithm on the $nr$ physical bits (the standing assumptions of Sections 3–5). Fix $0 < \eta < 1$ and an outer string $z$.
--
--   Let $h_0 = \varnothing, h_1, \dots, h_m$ be the histories of a path that ends at a terminal history, let $\xi_t = z_{J(h_t)}$, and let $P'_z(h_m)$ be the probability that Algorithm 1 follows this path.
--
--   1. If all denominators $\ell^{z_{J^+(h_t)}}_{h_t}$ ($t < m$) used by the simulator on the path are positive, then
--   $$
--   P'_z(h_m) = \ell^{\xi_m}_{h_m} \prod_{t=0}^{m-1} \frac{\ell^{\xi_t}_{h_t}}{\ell^{\xi_{t+1}}_{h_t}} . \tag{5.2}
--   $$
--   2. If every history on the path is good for $z$, then all these denominators are positive, and whenever $\ell_{h_m}(z) > 0$,
--   $$
--   P'_z(h_m) \ge (1 + \eta)^{-(n+1)}\, \ell_{h_m}(z). \tag{5.3}
--   $$
--
--   Between two revelations the averaged likelihoods cancel exactly, so only the at most $n$ steps that reveal a block cost a factor.
--
--   Differences from the source:
--   - encoding: histories as sequences of outcomes, hy the child, v ≺ h the strict ancestors → lists of recorded outcomes (Step), h ++ [encodeStep y] the child, proper prefixes the strict ancestors; reason: the record determines the outcome (decodeStep ∘ encodeStep = some), so histories correspond one to one
--   - encoding: partial assignments ξ ∈ {0,1}^J and ζ ∈ {0,1}^Ī → full strings Fin n → Bool read only on J (resp. outside I); averages over full strings; reason: the quantities depend only on the restriction; the average over ζ replicates each restriction 2^|I| times uniformly
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Lemma 5.1, p.18 (PDF p.20); η fixed in (0,1) as on p.17 (PDF p.19)

import Definitions.Def_HybridXorLift_simProb
import Definitions.Def_HybridXorLift_IsGood
import Definitions.Def_HybridXorLift_ParallelHybridAlg_terminals
import Definitions.Def_HybridXorLift_ParallelHybridAlg_SlotsAtMost

namespace HybridXorLift

/-- Lemma 5.1 (Telescoping) of Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), p.18 (PDF p.20), for every fixed `0 < η < 1` (p.17 (PDF
p.19): "We fix 0 < η < 1"). Let `h_0 = ∅, h_1, …, h_m` be the histories of a path that ends at a
terminal history and `ξ_t = z_{J(h_t)}`. If all denominators `ℓ^{z_{J⁺(h_t)}}_{h_t}` used by the
simulator on the path are positive, then
`P′_z(h_m) = ℓ^{ξ_m}_{h_m} ∏_{t<m} ℓ^{ξ_t}_{h_t} / ℓ^{ξ_{t+1}}_{h_t}` (5.2). If every history on the path
is good for `z`, then all these denominators are positive, and whenever `ℓ_{h_m}(z) > 0`,
`P′_z(h_m) ≥ (1 + η)^{−(n+1)} ℓ_{h_m}(z)` (5.3).

**Formalization Note** The standing assumptions of §§3–5 (p.11 (PDF p.13): "we fix integers n ≥ 1, r ≥ 1, q ≥ 1 and a parallel q-query hybrid algorithm on nr physical bits") are explicit hypotheses. Histories are lists of recorded outcomes (`ParallelHybridAlg.histories`); partial assignments are full functions read only on their index set (`cubeAvg`). The path is the list of prefixes `l.take t`, `t ≤ m = |l|`, of
a terminal history `l`; `P′_z` is `simProb`. -/
theorem lemma_5_1 {n r : ℕ} {α : Type} (hn : 1 ≤ n) (hr : 1 ≤ r) (q : ℕ) (hq : 1 ≤ q)
    (A : ParallelHybridAlg (Fin n × Fin r) α) (hA : A.SlotsAtMost q)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (z : Fin n → Bool)
    (l : List (Step (Fin n × Fin r))) (hl : l ∈ A.terminals) :
    ((∀ t < l.length, 0 < avgLikelihood A (l.take t) (revealedNext A (l.take t)) z) →
      simProb A z l = avgLikelihood A l (revealed A l) z *
        ∏ t ∈ Finset.range l.length,
          avgLikelihood A (l.take t) (revealed A (l.take t)) z /
            avgLikelihood A (l.take t) (revealed A (l.take (t + 1))) z) ∧
    ((∀ t ≤ l.length, IsGood A q η z (l.take t)) →
      (∀ t < l.length, 0 < avgLikelihood A (l.take t) (revealedNext A (l.take t)) z) ∧
      (0 < likelihood A l z → ((1 + η) ^ (n + 1))⁻¹ * likelihood A l z ≤ simProb A z l)) := by sorry

end HybridXorLift
