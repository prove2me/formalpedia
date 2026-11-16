-- Prove2me | Theorems.Thm_MatrixSenseRank_Testing_Supplement_lemma_9
-- name    : MatrixSenseRank.Testing.Supplement.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:11:16.223969+00:00
-- url     : https://prove2.me/theorems/1ddf90e6-ed0a-4d98-8999-3096497ee2a7
-- title:
--   Lemma 9 — chi-squared bound for the no prior
-- statement:
--   There are absolute constants $c_0,C>0$ such that, for every $n\ge2$ and integer $1\le T\le c_0n$,
--
--   $$\chi^2(P_{D_{\rm no},T}\Vert Q_T)\le C\frac{T}{n}.$$
--
--   Here a single target is first drawn from Definition 6's prior and shared by all $T$ full-Gaussian noiseless observations; $Q_T$ has independent standard Gaussian labels and designs. The divergence is extended valued, with $+\infty$ for singular measures. Absolute continuity and finite divergence are consequences of this bound.
--
--   This is the no-prior comparison used in Theorem 1. The constants are chosen before the dimension and sample count, including the finite small-dimensional cases where the positive-sample range can be empty.
--
--   Differences from the source:
--   - encoding: absolute asymptotic constants and sufficiently large dimensions → existential constants and thresholds preceding every dimension, accuracy, sample count and test; reason: the constants are uniform; no numerical coefficient is invented
--   - encoding: chi-squared divergence with Appendix B's extended convention → an extended nonnegative Radon–Nikodym integral, with infinity when absolute continuity fails; reason: no integrability or absolute-continuity hypothesis is assumed; the source defines T at least one
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, Matrix sensing meets property testing: Sample-optimal testing for low rank, STOC 2027 submission #380 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf, PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b; Lemma 9, printed p. 14, PDF p. 15 (1-based).

import Definitions.Def_MatrixSenseRank_Testing_Supplement_Priors

set_option autoImplicit false

namespace MatrixSenseRank.Testing.Supplement

/-- Lemma 9, printed p.14 / PDF p.15. The divergence may be infinite by definition;
its finiteness is a conclusion. Absolute constants precede all instances. -/
theorem lemma_9 :
    ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧
      ∀ n T : ℕ, 2 ≤ n → 1 ≤ T → (T : ℝ) ≤ c₀ * n →
        chiSquared (priorSamples (noPrior n) T) (nullSamples n T) ≤
          ENNReal.ofReal (C * T / n) := by sorry

end MatrixSenseRank.Testing.Supplement
