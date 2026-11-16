-- Prove2me | Theorems.Thm_GPTIP632_Classical_Supplement_lemma_G_2
-- name    : GPTIP632.Classical.Supplement.lemma_G_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:21:47.140084+00:00
-- url     : https://prove2.me/theorems/5d3ef52f-3c31-4fdf-a696-6d41dfde0b60
-- title:
--   Lemma G.2 — approximating v from a decider, including its space bound
-- statement:
--   Let $v\in(0,1)$. For a nonempty bit string $t=t_1\cdots t_m$, write $\bar t=\sum_{j=1}^m t_j2^{-j}$, and let $L_v$ have yes-instances satisfying $\bar t+m^{-2}\le v$ and no-instances satisfying $v\le\bar t-m^{-2}$. If a total decision function $D$ is correct on these two sets, put $w_m=\max\{\bar t:|t|=m,\ D(t)=1\}$, with $w_m=0$ when the set is empty. Then for every $m\ge1$,
--
--   $$|v-w_m|<m^{-2}+2^{-m}.$$
--
--   Moreover, for every deterministic total machine $D$ using at most $s(m)\ge m$ cells on all inputs of length $m$, there are a constant $c>0$ and one transducer that, on input $1^m$, halts and outputs the $m$ binary digits of $w_m$ within $c\,s(m)$ cells for every $m\ge1$. This assertion holds whether or not the total machine decides a comparison promise problem, and in particular applies to every decider above. The constant and transducer are chosen after $D,s$ and before $m$.
--
--   This lemma recovers approximations to the coordinate $v$ from a decider; both its strict error estimate and its space assertion are retained.
--
--   Differences from the source:
--   - generalization: D is a total algorithm deciding L_v → the numerical bound permits any total Boolean function deciding L_v; the output-space assertion applies to every total space-bounded OTM, independently of promise correctness; reason: the numerical estimate uses only the values of D, while enumerating accepted strings uses only totality and the space bound
--   - encoding: binary fractions and the largest accepted m-bit fraction, or zero → exact rationals with denominator 2^m, a finite maximum of natural numerators with bottom zero, and exactly m output bits in most-significant-first order; reason: this preserves each binary fraction and the empty-acceptance convention without an unbounded real supremum
--   - encoding: positive string lengths and O(s(m)) space → m >= 1, an empty-oracle OTM with input and query cells counted, and an existential positive natural c with output space at most c*s(m); reason: the comparison problem excludes empty strings, and s(m) >= m absorbs fixed overhead for positive m; c is uniform in m and depends only on D and s
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.33 (PDF p.35), Lemma G.2

import Mathlib
import Definitions.Def_GPTIP632_Classical_Supplement_BinaryComparison
import Definitions.Def_GPTIP632_Classical_Supplement_SpaceTransducer

namespace GPTIP632.Classical.Supplement

theorem lemma_G_2 :
    (∀ (v : ℝ), 0 < v → v < 1 → ∀ D : List Bool → Bool,
      DecidesComparison D v → ∀ m : ℕ, 1 ≤ m →
        |v - (acceptedMaximum D m : ℝ)| < 1 / (m : ℝ) ^ 2 + 1 / (2 : ℝ) ^ m) ∧
    (∀ (D : QAdvFew.PoQOracle.OTM) (s : ℕ → ℕ),
      (∀ m : ℕ, m ≤ s m) → TotalInSpace D s →
      ∃ c : ℕ, 0 < c ∧ ∃ A : QAdvFew.PoQOracle.OTM,
        ComputesUnaryInSpace A (acceptedDigits (machineDecision D)) (fun m => c * s m)) := by sorry

end GPTIP632.Classical.Supplement
