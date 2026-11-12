-- Prove2me | Theorems.Thm_OracleSNARG_PublicLB_final_display
-- name    : OracleSNARG.PublicLB.final_display
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:49:23.516196+00:00
-- url     : https://prove2.me/theorems/d3a4d1e6-a667-4d04-8b43-3184bbe8b50d
-- title:
--   §6, final display — $\Pr_{h,r,\mathrm{crs}}[C^{O_{h,r}}(x_{\mathrm{crs}})=0\wedge V^{O_{h,r}}(\mathrm{crs},x_{\mathrm{crs}},\pi_{\mathrm{crs},r})=1]\ge(1-\mathrm{negl}(\lambda))/(4\ell)$
-- statement:
--   Let $S=(\mathrm{Gen},P,V)$ be a scheme for the majority computation with adaptive completeness. Let $n$ be polynomially bounded and $N(\lambda)$ odd. Let the verifier make at most $\ell(\lambda)$ oracle queries on every input and against every oracle, where $2^{k(\lambda)}=2\ell(\lambda)$, so $\ell(\lambda)$ is a power of two. Suppose that for all sufficiently large $\lambda$, $8\ell(\lambda)\le N(\lambda)$ and every $\mathrm{crs}$ in the support of $\mathrm{Gen}(1^\lambda)$ has $|\mathrm{crs}|<n(\lambda)$. For each $\lambda$ let $H_\lambda$ be a pairwise-independent family of functions $\{0,1\}^{n(\lambda)}\to\{0,1\}^{k(\lambda)}$.
--
--   Then there is a negligible function $\nu$ such that for every $\lambda$
--   $$\Pr_{h\leftarrow H_\lambda,\ r,\ \mathrm{crs}\leftarrow\mathrm{Gen}(1^\lambda)}\Big[C^{O_{h,r}}(x_{\mathrm{crs}})=0\ \wedge\ V^{O_{h,r}}(\mathrm{crs},x_{\mathrm{crs}},\pi_{\mathrm{crs},r})=1\Big]\ \ge\ \frac{1-\nu(\lambda)}{4\ell(\lambda)},$$
--   where $h$, the uniform prover coins $r$ and $\mathrm{crs}$ are sampled independently.
--
--   This is the last displayed step of the proof of Theorem 22. It combines Equation (4) with the pairwise-independence bound and the analysis of the event $E_{\mathrm{crs},r}$.
--
--   Differences from the source:
--
--   - generalization: "V makes ℓ ≤ N/8 queries" and "n > |crs|" (footnote 7) for every λ → ℓ(λ) ≤ N(λ)/8 and |crs| < n(λ) required only for all sufficiently large λ; reason: the conclusion holds up to a negligible ν, which absorbs finitely many λ
--   - generalization: Gen and V polynomial-time (Definition 9) → Gen any distribution on bit strings without oracle access, V any deterministic oracle procedure; reason: the step never uses their running time, so it covers more schemes
--   - generalization: the honest prover P polynomial-time and N = N(λ) polynomially bounded (Definition 9; proof of Theorem 22) → neither assumed; reason: the step uses only adaptive completeness for the chooser crs ↦ x_crs, which needs n, not N or P, to be polynomially bounded, so it covers more schemes
--   - encoding: ℓ a power of 2 (footnote 9) and k = log2(2ℓ) → the hypothesis 2^{k(λ)} = 2ℓ(λ) for every λ; reason: the same condition, with k a function of λ
--   - encoding: the prover's random tape r → a uniform coin vector of the prover's circuit P_λ; reason: Lean convention for a polynomial-size randomized algorithm
-- source:
--   Goldwasser, Kalai, Incrementally Verifiable Oracle Aided Computation, STOC 2027 submission (manuscript sha256 cc66f0af…), p. 26, §6, display after 'Together with Equation (4), this gives'

import Mathlib
import Definitions.Def_OWFLocalDesc_Negligible
import Definitions.Def_OracleSNARG_PublicLB_Scheme
import Definitions.Def_OracleSNARG_PublicLB_ProofObjects

set_option autoImplicit false

namespace OracleSNARG.PublicLB

/-- **§6, final display**, p. 26 of Goldwasser, Kalai (manuscript sha256 cc66f0af…): "Together
with Equation (4), this gives Pr_{h,r,crs←Gen(1^λ)}[C^{O_{h,r}}(x_crs) = 0 ∧
V^{O_{h,r}}(crs, x_crs, π_{crs,r}) = 1] ≥ (1 − negl(λ))/(4ℓ). Here h, r, crs, are sampled
independently." Under the proof's standing assumptions: adaptive completeness, `n` polynomially
bounded, `N` odd, a verifier making at most `ℓ(λ)` queries on every input with `ℓ(λ)` a power of
two (`2^{k(λ)} = 2ℓ(λ)`), and, for all sufficiently large `λ`, `ℓ ≤ N/8` and `n > |crs|`; `h` is
drawn from a pairwise-independent family `{0,1}^n → {0,1}^k` for each `λ`. -/
theorem final_display (n N ℓ k : ℕ → ℕ) (S : Scheme) (hn : PolyBounded n)
    (hodd : ∀ lam, Odd (N lam))
    (hV : ∀ lam crs x π, (S.verifier lam crs x π).depth ≤ ℓ lam)
    (hk : ∀ lam, 2 ^ k lam = 2 * ℓ lam)
    (hℓN : ∀ᶠ lam in Filter.atTop, 8 * ℓ lam ≤ N lam)
    (hcrs : ∀ᶠ lam in Filter.atTop, ∀ crs ∈ (S.gen lam).support, crs.length < n lam)
    (hcompl : AdaptiveComplete n N S)
    (H : ∀ lam, PMF (Hash (n lam) (k lam))) (hH : ∀ lam, IsPairwiseIndep (H lam)) :
    ∃ ν : ℕ → ℝ, OWFLocalDesc.Negligible ν ∧
      ∀ lam : ℕ, (1 - ν lam) / (4 * (ℓ lam : ℝ)) ≤ (finalExp S n N lam (H lam) true).toReal := by sorry

end OracleSNARG.PublicLB
