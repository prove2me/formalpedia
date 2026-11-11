-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_sampling_residual
-- name    : MaxCutMatrix2027.Upper.sampling_residual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T12:48:11.118922+00:00
-- url     : https://prove2.me/theorems/dc11c861-2f7f-4aef-b7b4-0d6930734d34
-- title:
--   Lemma 4.3 — Sampling the spectral residual
-- statement:
--   There is one absolute constant $C_{\mathrm{res}}>0$ with the following property. Let $G$ be any simple graph on $n$ vertices, let $1\le s\le n$ be real, and let $0<\tau\le1$. Form the spectral residual $R=A-\sum_{|\theta_j|>\tau n}\theta_j u_ju_j^T$. If $P$ has independent Bernoulli$(s/n)$ diagonal entries, then
--   $$\frac1{s^2}\mathbb E\sup_{x\in[-1,1]^n}|x^TPRPx|\le C_{\mathrm{res}}\left(\tau+\frac1{\tau s}+\frac1{\sqrt s}\right).$$
--   The residual is computed from the adjacency matrix; neither its diagonal estimate nor any norm bound is supplied as a premise. The supremum is over the continuous cube. The proof gives $C_{\mathrm{res}}=2C_{\mathrm{RV}}$, uniformly over all instances. This controls the sampling error contributed by discarding the residual.
--
--   Differences from the source:
--   - encoding: vertices labelled by [n] and independent Bernoulli selectors → Fin n and the exact finite Bernoulli-subset expectation; reason: relabeling is bijective and the subset weights are exactly the independent-selector law
--   - encoding: any orthonormal eigenbasis for the spectral truncation → Mathlib's chosen orthonormal eigenbasis; reason: the retained spectral operator is the same on each eigenspace, so the construction is basis-independent
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Lemma 4.3, p.19 (PDF p.19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_MatrixModel
set_option autoImplicit false

namespace MaxCutMatrix2027.Upper

/-- Lemma 4.3, p.19, with all standing hypotheses from p.18. -/
theorem sampling_residual :
    ∃ C_res : ℝ, 0 < C_res ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s τ : ℝ),
      1 ≤ s → s ≤ n → 0 < τ → τ ≤ 1 →
      sampleAverage (s / n) (fun Q => cubeAbsSup (restrictMatrix Q (residualMatrix G τ))) / s ^ 2 ≤
        C_res * (τ + 1 / (τ * s) + 1 / Real.sqrt s) := by sorry

end MaxCutMatrix2027.Upper
