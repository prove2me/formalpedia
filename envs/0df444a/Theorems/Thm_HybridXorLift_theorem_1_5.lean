-- Prove2me | Theorems.Thm_HybridXorLift_theorem_1_5
-- name    : HybridXorLift.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:16:53.5489+00:00
-- url     : https://prove2.me/theorems/901ea26d-ef6d-47de-bc33-3326cdb018f2
-- title:
--   Theorem 1.5 — parallel $q$-query hybrid algorithms for $f\circ\mathrm{XOR}_r$ cost at least $rR(f)/2500$ when $r \ge 100q\ln(n+2)$
-- statement:
--   Let $f : D \to \{0,1\}$ be a partial Boolean function with $D \subseteq \{0,1\}^n$, and let $q \ge 1$. Every hybrid algorithm whose subroutines are parallel with at most $q$ queries each, and which computes $f \circ \mathrm{XOR}_r$ with error at most $1/3$ on every promised input, has
--   $$
--   \mathrm{cost} \ \ge\ \frac{r\, R(f)}{2500}
--   $$
--   whenever $r \ge 100\, q \ln(n + 2)$. Here $R(f)$ is the bounded-error randomized query complexity of $f$ (worst-case number of queries, error at most $1/3$ on every promised input).
--
--   The constant does not depend on $q$: making several queries at the same time gives no asymptotic advantage over reading whole blocks classically, provided the blocks grow linearly with $q$.
--
--   **Formalization Note** $R(f)$ is the published randomized query complexity `NoPerfectRandComp.R`; $\ln$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: a subroutine starts from an input-independent (possibly mixed) state and ends with an arbitrary measurement → a pure unit start state on query register(s) × workspace Fin w, input-independent unitaries, and a complete computational-basis measurement with one child per outcome; reason: §2.2: purifying every preparation and dilating every measurement change neither the cost nor the output distribution, so the class of algorithms is the paper's
--   - encoding: error at most 1/3 on every promised input → probability at least 2/3 of outputting the correct bit on every promised input; reason: the outputs are bits, whose probabilities sum to one
--   - encoding: physical bits x_ij with i ∈ [n], j ∈ [r], bits in {0,1} → functions Fin n × Fin r → Bool, 0-based block and position; reason: Lean convention; same instances
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Theorem 1.5, p.3 (PDF p.5)

import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_HybridXorLift_xorComp
import Definitions.Def_HybridXorLift_ParallelHybridAlg_outProb
import Definitions.Def_HybridXorLift_ParallelHybridAlg_cost
import Definitions.Def_HybridXorLift_ParallelHybridAlg_SlotsAtMost

namespace HybridXorLift

/-- Theorem 1.5 (Parallel subroutines) of Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), p.3 (PDF p.5). Let `f : D → {0,1}` with
`D ⊆ {0,1}ⁿ`, and let `q ≥ 1`. Every hybrid algorithm whose subroutines are parallel with at
most `q` queries each, and which computes `f ∘ XOR_r` with error at most `1/3` on every promised
input, has cost at least `r R(f)/2500` whenever `r ≥ 100 q ln(n + 2)`.

**Formalization Note** `R(f)` is the published `NoPerfectRandComp.R` (worst-case depth, error at
most `1/3` on every promised input). Error at most `1/3` on a promised input `x` is written as
probability at least `2/3` of outputting `(f ∘ XOR_r)(x) = f(σ(x))`. -/
theorem theorem_1_5 {n : ℕ} (f : NoPerfectRandComp.PartialFn (Fin n)) (q r : ℕ) (hq : 1 ≤ q)
    (hrq : 100 * (q : ℝ) * Real.log ((n : ℝ) + 2) ≤ r)
    (A : ParallelHybridAlg (Fin n × Fin r) Bool) (hA : A.SlotsAtMost q)
    (hcorr : ∀ x ∈ (xorComp f r).dom, 2 / 3 ≤ A.outProb x ((xorComp f r).val x)) :
    (r : ℝ) * (NoPerfectRandComp.R f : ℝ) / 2500 ≤ A.cost := by sorry

end HybridXorLift
