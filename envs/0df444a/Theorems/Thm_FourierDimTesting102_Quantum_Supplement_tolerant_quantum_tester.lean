-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_Supplement_tolerant_quantum_tester
-- name    : FourierDimTesting102.Quantum.Supplement.tolerant_quantum_tester
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:31:18.247573+00:00
-- url     : https://prove2.me/theorems/4baddc0d-6e89-4138-a058-746852aeebbc
-- title:
--   Theorem 5.1 — a tolerant quantum tester with $O(\frac{k}{\epsilon(1-2\alpha)^2}\log\frac1{\epsilon(1-2\alpha)})$ queries
-- statement:
--   Let $0\le\alpha<1/2$ and $0<\epsilon<1/2$ (Definition 2.6). There is a quantum query algorithm, with oracle $O_f:|x\rangle|b\rangle\mapsto|x\rangle|b\oplus f(x)\rangle$, that on every branch makes at most
--
--   $$
--   C\,\frac{k+1}{\epsilon(1-2\alpha)^2}\,\log\frac{1}{\epsilon(1-2\alpha)}
--   $$
--
--   queries, for an absolute constant $C$ independent of $n,k,\alpha,\epsilon$ (for $k\ge1$ at most $2C\frac{k}{\epsilon(1-2\alpha)^2}\log\frac1{\epsilon(1-2\alpha)}$), and for every boolean $f$ on $\mathbb F_2^n$:
--
--   1. if $\operatorname{dist}(f,D_k)\le\alpha\epsilon$, it accepts with probability at least $2/3$;
--   2. if $\operatorname{dist}(f,D_k)\ge\epsilon$, it rejects with probability at least $2/3$.
--
--   So tolerant testing costs only a logarithmic factor and the loss of the square-root saving in $\epsilon$ compared with Theorem 3.1. The denominator shows why $\alpha<1/2$ is needed.
--
--   Differences from the source:
--   - encoding: boolean functions f : F₂ⁿ → {−1,1} → f is its bit function BoolFn n := (Fin n → ZMod 2) → Bool, with sign toSign f x = (−1)^{f x} (the base Model); reason: a bijection on the same functions; the bit is what the oracle returns
--   - encoding: a quantum tester with oracle O_f : |x⟩|b⟩ → |x⟩|b ⊕ f(x)⟩ (Definition 2.5) → an AdaptiveQueryAlg (V n) Bool: frozen query rounds with the published XOR oracle, arbitrary finite workspaces, full computational-basis measurements and classical branching; output true is accept; reason: covers unitary algorithms (one round), intermediate measurements and classical coins (zero-query rounds), as in the base mission
--   - encoding: uses O(·) quantum queries → worstCaseQueries A, the largest number of queries over all branches of the algorithm’s tree, positive-probability or not; reason: the all-branch count is at least the count over positive-probability runs on any input, so the bound is the strongest form
--   - generalization: O(k/(ϵ(1−2α)²) log(1/(ϵ(1−2α)))) for fixed α, ϵ (0 at k = 0) → C(k+1)/(ε(1−2α)²) · log(1/(ε(1−2α))) for every k ≥ 0, one absolute C for all α, ε in range; reason: for k ≥ 1, k + 1 ≤ 2k gives the source’s bound; the bound also covers k = 0 and is uniform in α and ε
--   - reading: distance at most αϵ / at least ϵ from having Fourier dimension at most k → distToSet f (Dk n k) ≤ α·ε / ≥ ε; reason: Definition 2.6 verbatim, with distance to D_k the minimum over its members
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.23, Theorem 5.1 (Algorithm 3, p.24; proof pp.24–26 with Lemma 5.1)

import Definitions.Def_FourierDimTesting102_Quantum_Algorithm

namespace FourierDimTesting102.Quantum.Supplement

open QAlgorithms FourierDimTesting102.Quantum

/-- Theorem 5.1, p.23: there is an absolute constant `C` such that for all `n`, `k`, and all
`0 ≤ α < 1/2`, `0 < ε < 1/2` (Definition 2.6), some adaptive quantum query algorithm `A` makes at
most `C (k+1)/(ε(1−2α)²) · log(1/(ε(1−2α)))` queries on every branch, accepts (`true`) every `f`
with `dist(f, D_k) ≤ αε` with probability at least `2/3`, and rejects (`false`) every `f` with
`dist(f, D_k) ≥ ε` with probability at least `2/3`. -/
theorem tolerant_quantum_tester :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) (α ε : ℝ), 0 ≤ α → α < 1 / 2 → 0 < ε → ε < 1 / 2 →
      ∃ A : AdaptiveQueryAlg (V n) Bool,
        (worstCaseQueries A : ℝ) ≤ C * ((k : ℝ) + 1) / (ε * (1 - 2 * α) ^ 2) *
            Real.log (1 / (ε * (1 - 2 * α))) ∧
        ∀ f : BoolFn n,
          (distToSet f (Dk n k) ≤ α * ε → 2 / 3 ≤ A.outProb f true) ∧
          (ε ≤ distToSet f (Dk n k) → 2 / 3 ≤ A.outProb f false) := by sorry

end FourierDimTesting102.Quantum.Supplement
