-- Prove2me | Theorems.Thm_OptimalSpectrum_Entangled_lemma_A_1
-- name    : OptimalSpectrum.Entangled.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:05.841198+00:00
-- url     : https://prove2.me/theorems/d8f1ae6e-3c58-4b94-a9e8-d97601d2632c
-- title:
--   Lemma A.1 — derivative bounds for $\phi_k$ and $\psi_k$
-- statement:
--   Let $L>0$. For $1\le r\le k$,
--
--   $$\frac{\|\phi_k^{(r)}\|_{\infty,[0,L]}}{r!}\le\frac{(4k^2/L)^r}{(2r)!},\qquad \frac{\|\psi_k^{(r)}\|_{\infty,[0,L]}}{r!}\le\frac{(2k/L)^r}{r!}.$$
--
--   The interior basis has derivatives growing like $k^r$ instead of $k^{2r}$; substituted into Lemma 7.1 these bounds give Corollary 7.2.
--
--   **Formalization Note** The printed proof of the second bound loses a factor $2^r$ (it yields $(4k/L)^r/r!$); the statement as printed is the target.
--
--   Differences from the source:
--   - encoding: L > 0 fixed in the §6 Setup → L > 0 as a binder; reason: standing assumption
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Lemma A.1, p. 30 (PDF p. 32)

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_phiPoly
import Definitions.Def_OptimalSpectrum_Entangled_psiPoly
import Definitions.Def_OptimalSpectrum_Entangled_supNormDeriv

namespace OptimalSpectrum.Entangled

/-- **Lemma A.1 (Chebyshev derivative bounds).**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Lemma A.1, printed p. 30 (PDF p. 32): "For 1 ⩽ r ⩽ k,
∥ϕ_k^(r)∥_(∞,[0,L])/r! ⩽ (4k²/L)^r/(2r)!, ∥ψ_k^(r)∥_(∞,[0,L])/r! ⩽ (2k/L)^r/r!."

**Formalization Note.** `L > 0` is the standing assumption of §6. The printed proof of the second
bound (printed p. 31) yields `(4k/L)^r/r!`; the statement as printed, `(2k/L)^r/r!`, is the target. -/
theorem lemma_A_1 (L : ℝ) (hL : 0 < L) (k r : ℕ) (hr1 : 1 ≤ r) (hrk : r ≤ k) :
    supNormDeriv (phiPoly L k) r L / r.factorial ≤ (4 * (k : ℝ) ^ 2 / L) ^ r / (2 * r).factorial ∧
    supNormDeriv (psiPoly L k) r L / r.factorial ≤ (2 * (k : ℝ) / L) ^ r / r.factorial := by sorry

end OptimalSpectrum.Entangled
