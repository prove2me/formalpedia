-- Prove2me | Theorems.Thm_IntQuotHNP_lemma_4_4
-- name    : IntQuotHNP.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:54:02.927875+00:00
-- url     : https://prove2.me/theorems/ade5ca4f-7e7c-46f2-980c-7a9be05c3d99
-- title:
--   Lemma 4.4 — tail bound $\Pr[Z_{\mathrm{target}}>u]\le\Psi_X(u)$
-- statement:
--   For every $N\ge3$ there is $C_N>0$, depending only on $N$, such that for every function $p\mapsto X(p)\ge1$ with $X(p)^2/p\to0$ there is $p_0$ with the following property. For every prime $p\ge p_0$, every secret $y^*\in\mathbb Z_p$ and every real $1\le u\le X(p)$, under the sampling rule, with $Z_{\mathrm{target}}$ taken for the lattice (6) and $v_{\mathrm{tar}}$ of the sampled input,
--   $$
--   \Pr[Z_{\mathrm{target}}>u]\le\Psi_{X(p)}(u),
--   $$
--   where $\Psi_X$ is (7) with the constant $C_N$. This is the central probabilistic estimate of the mission.
--
--   Differences from the source:
--   - reading: integers X = X(p) ≥ 1 with X² = o(p) → a function Xf : ℕ → ℕ with values ≥ 1 and Xf(p)²/p → 0 along all natural numbers; C_N before the function, p₀ after it; reason: a function given on primes extends by the value 1 elsewhere without changing the limit, so no instance is lost; the source says C_N depends only on N
--   - generalization: a fixed secret y* of the sampling rule, with p sufficiently large → p₀ chosen before y*, so the bound holds for every y* < p at once; reason: the uniform statement specializes to each fixed y*; Theorem 4.2 asks for this uniformity ("uniformly for every fixed y*") and Ψ_X does not depend on y*
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), Lemma 4.4, eq. (7), p.23 (PDF p.24)

import Mathlib
import Definitions.Def_IntQuotHNP_Sampling
import Definitions.Def_IntQuotHNP_DualLattice
import Definitions.Def_IntQuotHNP_MIHNPLattice
import Definitions.Def_IntQuotHNP_Psi

open Filter Topology

namespace IntQuotHNP

/-- **Lemma 4.4 (tail bound for short dual vectors).**
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), Lemma 4.4, p.23 (PDF p.24): "Fix N ≥ 3 and integers X = X(p) ≥ 1 with X² = o(p). Under
the sampling rule above, for sufficiently large p and every 1 ≤ u ≤ X, Pr[Z_target > u] ≤ Ψ_X(u),
where E_j(u) = (X²/(pu))^j + p^{−1/2} for j ∈ [N] and
Ψ_X(u) = C_N ∑_{κ=1}^N (X/u)^κ ∏_{j=1}^{κ−1} E_j(u) E_κ(u)^{N−κ}. (7) C_N depends only on N."

For every `N ≥ 3` there is `C_N > 0` such that for every function `p ↦ X(p) ≥ 1` with
`X(p)²/p → 0` there is `p₀` with: for every prime `p ≥ p₀`, every secret `y∗ ∈ ℤ_p` and every real
`1 ≤ u ≤ X(p)`, the probability over the sampled shifts that `Z_target > u` (for the lattice (6) and
`v_tar` of the sampled input) is at most `Ψ_{X(p)}(u)` with constant `C_N`.

**Formalization Note.** `X² = o(p)` is read for an arbitrary integer function `X(p)`; `C_N` is chosen
before `X(·)` and depends only on `N`, `p₀` may depend on `N` and `X(·)`. The bound holds uniformly
in `y∗` and `u`. -/
theorem lemma_4_4 (N : ℕ) (hN : 3 ≤ N) :
    ∃ CN : ℝ, 0 < CN ∧ ∀ Xf : ℕ → ℕ, (∀ p, 1 ≤ Xf p) →
      Tendsto (fun p : ℕ => ((Xf p : ℝ) ^ 2 / p)) atTop (𝓝 0) →
      ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ ≤ p → ∀ y, y < p → ∀ u : ℝ, 1 ≤ u → u ≤ Xf p →
        prob (shifts p N y) (fun t =>
            u < zTarget (latticeBasis (sampledInput p (Xf p) N y t))
              (vtar (sampledInput p (Xf p) N y t)) p) ≤
          Psi N CN (Xf p) p u := by sorry

end IntQuotHNP
