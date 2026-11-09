-- Prove2me | Theorems.Thm_HybridXorLift_lemma_5_2
-- name    : HybridXorLift.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:28:48.923878+00:00
-- url     : https://prove2.me/theorems/0574a9f1-3231-4b76-9ae3-c281ba0ee5bb
-- title:
--   Lemma 5.2 — bad histories are rare: $B_z < 10^{-3}$
-- statement:
--   Throughout, $n \ge 1$, $r \ge 1$, $q \ge 1$ are integers and $A$ is a parallel $q$-query hybrid algorithm on the $nr$ physical bits (the standing assumptions of Sections 3–5).
--
--   Let $\eta = 1/(1000(n+1))$ (5.5) and let $B_z$ be the probability that the true process (a uniformly random $x \in \sigma^{-1}(z)$) reaches a history that is bad for $z$. If $n \ge 1$ and $r \ge 100\, q \ln(n + 2)$, then
--   $$
--   B_z < 10^{-3}
--   $$
--   for every outer string $z$.
--
--   **Formalization Note** $\ln$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: histories as sequences of outcomes, hy the child, v ≺ h the strict ancestors → lists of recorded outcomes (Step), h ++ [encodeStep y] the child, proper prefixes the strict ancestors; reason: the record determines the outcome (decodeStep ∘ encodeStep = some), so histories correspond one to one
--   - encoding: partial assignments ξ ∈ {0,1}^J and ζ ∈ {0,1}^Ī → full strings Fin n → Bool read only on J (resp. outside I); averages over full strings; reason: the quantities depend only on the restriction; the average over ζ replicates each restriction 2^|I| times uniformly
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Lemma 5.2, p.18 (PDF p.20); η of Eq. (5.5)

import Definitions.Def_HybridXorLift_badProb
import Definitions.Def_HybridXorLift_ParallelHybridAlg_SlotsAtMost

namespace HybridXorLift

/-- Lemma 5.2 (Bad histories) of Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), p.18 (PDF p.20), with `η = 1/(1000(n + 1))` (5.5). If
`n ≥ 1` and `r ≥ 100 q ln(n + 2)`, then `B_z < 10⁻³` for every outer string `z`.

**Formalization Note** The standing assumptions of §§3–5 (p.11 (PDF p.13): "we fix integers n ≥ 1, r ≥ 1, q ≥ 1 and a parallel q-query hybrid algorithm on nr physical bits") are explicit hypotheses. `ln` is `Real.log`. -/
theorem lemma_5_2 {n r : ℕ} {α : Type} (hn : 1 ≤ n) (hr : 1 ≤ r) (q : ℕ) (hq : 1 ≤ q)
    (A : ParallelHybridAlg (Fin n × Fin r) α) (hA : A.SlotsAtMost q)
    (hrq : 100 * (q : ℝ) * Real.log ((n : ℝ) + 2) ≤ r) (z : Fin n → Bool) :
    badProb A q z < 1 / 1000 := by sorry

end HybridXorLift
