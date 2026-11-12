-- Prove2me | Theorems.Thm_OracleSNARG_PublicLB_equation_4
-- name    : OracleSNARG.PublicLB.equation_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:48:37.003717+00:00
-- url     : https://prove2.me/theorems/38fa9a99-23a6-4d4f-858e-859cfb172ecd
-- title:
--   §6, Equation (4) — completeness under the all-ones oracle: $\Pr_{\mathrm{crs},r}[V^{O_1}(\mathrm{crs},x_{\mathrm{crs}},\pi_{\mathrm{crs},r})=1]\ge 1-\mathrm{negl}(\lambda)$
-- statement:
--   Let $S=(\mathrm{Gen},P,V)$ be a scheme for the majority computation with adaptive completeness. Let $n$ be polynomially bounded and $N(\lambda)$ odd for every $\lambda$, and suppose that for all sufficiently large $\lambda$ every $\mathrm{crs}$ in the support of $\mathrm{Gen}(1^\lambda)$ has $|\mathrm{crs}|<n(\lambda)$. Then there is a negligible function $\nu$ such that for every $\lambda$
--   $$\Pr_{\mathrm{crs}\leftarrow\mathrm{Gen}(1^\lambda),\ r}\big[V^{O_1}(\mathrm{crs},x_{\mathrm{crs}},\pi_{\mathrm{crs},r})=1\big]\ \ge\ 1-\nu(\lambda),$$
--   where $r$ is uniform. Here $O_1$ is the all-ones oracle, $x_{\mathrm{crs}}=\mathrm{crs}\|1\|0^{n-|\mathrm{crs}|-1}$, and $\pi_{\mathrm{crs},r}=P^{O_1}(\mathrm{crs},x_{\mathrm{crs}};r)$.
--
--   This is the first step of the proof of Theorem 22: since $C^{O_1}(x)=1$ for every $x$, adaptive completeness applied to the chooser $\mathrm{crs}\mapsto x_{\mathrm{crs}}$ makes the honest proof accepted with overwhelming probability.
--
--   Differences from the source:
--
--   - generalization: "our assumption that n > |crs|" (footnote 7) → required only for all sufficiently large λ; reason: the conclusion is a negligible-function bound, which ignores finitely many λ, and the paper's |crs| = o(n) gives it only eventually
--   - generalization: Gen and V polynomial-time (Definition 9) → Gen any distribution on bit strings without oracle access, V any deterministic oracle procedure; reason: the step never uses their running time, so it covers more schemes
--   - generalization: the honest prover P polynomial-time and N = N(λ) polynomially bounded (Definition 9; proof of Theorem 22) → neither assumed; reason: the step uses only adaptive completeness for the chooser crs ↦ x_crs, which needs n, not N or P, to be polynomially bounded, so it covers more schemes
--   - encoding: the prover's random tape r → a uniform coin vector of the prover's circuit P_λ; reason: Lean convention for a polynomial-size randomized algorithm
-- source:
--   Goldwasser, Kalai, Incrementally Verifiable Oracle Aided Computation, STOC 2027 submission (manuscript sha256 cc66f0af…), p. 25, §6, Equation (4) (with footnotes 6-8)

import Mathlib
import Definitions.Def_OWFLocalDesc_Negligible
import Definitions.Def_OracleSNARG_PublicLB_Scheme
import Definitions.Def_OracleSNARG_PublicLB_ProofObjects

set_option autoImplicit false

namespace OracleSNARG.PublicLB

/-- **§6, Equation (4)**, p. 25 of Goldwasser, Kalai (manuscript sha256 cc66f0af…): "Since
C^{O1}(x) = 1 for every x, Pr_{crs←Gen(1^λ), r}[V^{O1}(crs, x_crs, π_{crs,r}) = 1] ≥ 1 − negl(λ)",
from adaptive completeness (footnote 8) for the oracle `O₁` and the chooser `crs ↦ x_crs`, under the
proof's standing assumptions: `n` polynomially bounded, `N` odd (footnote 6) and `n > |crs|`
(footnote 7), the latter for all sufficiently large `λ`. -/
theorem equation_4 (n N : ℕ → ℕ) (S : Scheme) (hn : PolyBounded n)
    (hodd : ∀ lam, Odd (N lam))
    (hcrs : ∀ᶠ lam in Filter.atTop, ∀ crs ∈ (S.gen lam).support, crs.length < n lam)
    (hcompl : AdaptiveComplete n N S) :
    ∃ ν : ℕ → ℝ, OWFLocalDesc.Negligible ν ∧
      ∀ lam : ℕ, 1 - ν lam ≤ (eq4Exp S n lam true).toReal := by sorry

end OracleSNARG.PublicLB
