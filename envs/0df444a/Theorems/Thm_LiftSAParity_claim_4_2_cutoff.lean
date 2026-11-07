-- Prove2me | Theorems.Thm_LiftSAParity_claim_4_2_cutoff
-- name    : LiftSAParity.claim_4_2_cutoff
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:56.530622+00:00
-- url     : https://prove2.me/theorems/770bbed0-dbd9-44fb-ad66-682100e9e571
-- title:
--   Claim 4.2 — the cutoff $|I(J,A)|=d$ has probability at most $e^{-d/16\ell}$
-- statement:
--   Let $\ell\ge2$ and $d\ge2$, let $r$ be a natural number with $r\le d/2\ell$, and let $A\subseteq\{0,1\}^{n\times\ell}$ be a nonempty affine space of rank at most $r$. Then
--   $$\Pr_{J\sim[\ell]^n}\big[|I(J,A)|=d\big]\le\exp\Big(-\frac d{16\ell}\Big).$$
--
--   Reaching the $d$-th block requires at most $r-1$ pivots among the first $d-1$ iterations, while each iteration is a pivot with conditional probability at least $1/\ell$; a Chernoff bound gives the claim. It is the estimate behind items (2) and (3).
--
--   **Formalization Note** $I(J,A)$ is `blocks d J A`, which involves neither the local distribution nor the stifling inputs; $\ell\ge2$ is the standing hypothesis of §4.
--
--   Differences from the source:
--   - generalization: integers n ≥ 1 (§2, p.7) → n : ℕ, including n = 0; reason: at n = 0 the cube has a single point and the statement is degenerate; the Lean statement specializes to the printed one for n ≥ 1
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §4.2, p.15, Claim 4.2

import Mathlib
import Definitions.Def_LiftSAParity_IsAffineSpace
import Definitions.Def_LiftSAParity_blocks
import Definitions.Def_LiftSAParity_mu

namespace LiftSAParity

/-- **Claim 4.2** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary
Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §4.2, p.15): "For every d ≥ 2 and
every nonempty affine space A ⊆ {0, 1}^{n×ℓ} of rank at most r ≤ d/2ℓ,
Pr_J[|I(J, A)| = d] ≤ exp(−d/16ℓ)."

**Formalization Note** `ℓ ≥ 2` is the standing hypothesis of §4 (Theorem 4.1). `I(J, A)` is
`blocks d J A` (it involves neither `D` nor `γ`); `J` is uniform on `Fin n → Fin ℓ`. -/
theorem claim_4_2_cutoff {n ℓ d r : ℕ} (hℓ : 2 ≤ ℓ) (hd : 2 ≤ d)
    (hr : (r : ℝ) ≤ (d : ℝ) / (2 * (ℓ : ℝ))) (A : Set (Fin n × Fin ℓ → ZMod 2))
    (hA : IsAffineSpace A) (hne : A.Nonempty) (hcod : codim A ≤ r) :
    probJ (fun J : Fin n → Fin ℓ => (blocks d J A).card = d) ≤
      Real.exp (-(d : ℝ) / (16 * (ℓ : ℝ))) := by sorry

end LiftSAParity
