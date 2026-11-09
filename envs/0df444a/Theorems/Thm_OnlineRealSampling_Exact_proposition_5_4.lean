-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_proposition_5_4
-- name    : OnlineRealSampling.Exact.proposition_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:12:20.325804+00:00
-- url     : https://prove2.me/theorems/9718c9b1-a805-4f78-b091-2768eaa26af8
-- title:
--   Proposition 5.4 — the recycled state is uniform
-- statement:
--   Let $F$ have a valid oracle and $1\le M\le\Delta$.
--   1. Whenever Sample$(F,(Z,M),\Delta)$ halts with $0\le Z<M$, the recycled values satisfy $0\le Z'<M'\le\Delta$.
--   2. Let $Z$ be uniform on $\{0,\dots,M-1\}$, independent of the fair bits. Conditionally on $X$, $M$ and $M'$, the output $Z'$ is uniform on $\{0,\dots,M'-1\}$: for all $x$, $m'$ and $z'<m'$,
--   $$\Pr(X=x,\ M'=m',\ Z'=z')=\frac{\Pr(X=x,\ M'=m')}{m'}.$$
--
--   By induction over the iterations, this keeps the persistent state of Algorithm 2 a uniform random state.
--
--   Differences from the source:
--   - encoding: conditioned on the values of X, M and M′, Z′ is uniform → on the single-step space with M fixed, Pr(X = x, M′ = m′, Z′ = z′) = Pr(X = x, M′ = m′)/m′ for all x, m′ and z′ < m′; reason: conditioning on the fixed M is automatic; the identity is the definition of conditional uniformity on each fibre
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Proposition 5.4, PDF 11 / printed 10

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Algorithms

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Proposition 5.4 (the recycled state). For `1 ≤ M ≤ Δ`: the recycled values always satisfy
`0 ≤ Z' < M' ≤ Δ`; and with `Z ∼ Unif{0,…,M-1}` independent of the fair bits, conditionally on
`X`, `M` and `M'`, `Z'` is uniform on `{0,…,M'-1}`. -/
theorem proposition_5_4 (w : ℕ) (O : CDFOracle) (hO : O.Valid) (M Δ : ℕ) (hM : 1 ≤ M)
    (hMΔ : M ≤ Δ) :
    (∀ z : ℕ, z < M → ∀ (ω : ℕ → Bool) (out : SampleOut),
        sampleRun w O.toOracleAccess z M Δ ω = some out → out.Z' < out.M' ∧ out.M' ≤ Δ) ∧
      (∀ x m' z' : ℕ, z' < m' →
        stepMeasure M {p | ∃ out, sampleOn w O.toOracleAccess M Δ p = some out ∧ out.X = x ∧
            out.M' = m' ∧ out.Z' = z'} =
          stepMeasure M {p | ∃ out, sampleOn w O.toOracleAccess M Δ p = some out ∧ out.X = x ∧
            out.M' = m'} / (m' : ℝ≥0∞)) := by sorry

end OnlineRealSampling.Exact
