-- Prove2me | Theorems.Thm_MaskedLinx_lemma_2_9_eigenvalue_lower_bound
-- name    : MaskedLinx.lemma_2_9_eigenvalue_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:41:48.287749+00:00
-- url     : https://prove2.me/theorems/a07e9367-273b-4599-93d9-13b935bd07bc
-- title:
--   Lemma 2.9 — $\mathrm{linx}(C,s)\ge\tfrac12\log\prod_i\big(\tfrac sn\lambda_i^2+1-\tfrac sn\big)$
-- statement:
--   Let $C$ be a positive semidefinite real matrix of order $n$ with eigenvalues $\lambda_1,\dots,\lambda_n$ (with multiplicity), and let $s$ be an integer with $0<s<n$. Then the (unscaled) linx bound satisfies
--
--   $$\mathrm{linx}(C,s)\ \ge\ \frac12\log\prod_{i=1}^{n}\Big(\frac sn\lambda_i^2+1-\frac sn\Big).$$
--
--   Every factor of the product is at least $1-\tfrac sn>0$, so the right-hand side is a finite real number. The bound depends on $C$ only through its spectrum; it is the tool the paper uses to bound the unmasked linx bound from below, applied to $\sqrt\gamma\,C$ in the scaled case.
--
--   **Formalization Note** $\mathrm{linx}(C,s)$ is `linx C s 1`. The eigenvalues are Mathlib's `hC.isHermitian.eigenvalues`, in some order; the product does not depend on the order.
--
--   Differences from the source:
--   - encoding: linx(C,s) = max over P(n,s) of ½ ldet(C Diag(x) C + Diag(e − x)) → `linx C s 1`, an EReal supremum with ldet = ⊥ off the positive definite matrices; reason: Lean convention, the supremum is attained and equals the paper's maximum
-- source:
--   Chen, Fampa, Lee, Masking Anstreicher's linx bound for improved entropy bounds, arXiv:2106.02980v1, Lemma 2.9, p.6

import Mathlib
import Definitions.Def_MaskedLinx_linx

namespace MaskedLinx

/-- **Lemma 2.9 (eigenvalue lower bound on the linx bound).**
Chen, Fampa, Lee, *Masking Anstreicher's linx bound for improved entropy bounds*,
arXiv:2106.02980v1, Lemma 2.9, p.6:
"For any positive-semidefinite order-n matrix C and integer 0 < s < n,
linx(C,s) ≥ ½ log ∏_{i=1}^{n} ((s/n)λᵢ² + 1 − s/n), where λ1,...,λn are the eigenvalues of C."

**Formalization Note.** `linx(C,s)` is the unscaled bound (1), i.e. `linx C s 1`. The
eigenvalues are `hC.isHermitian.eigenvalues`, listed with multiplicity in some order (the product
does not depend on it). The product is positive, so `Real.log` is the true logarithm. -/
theorem lemma_2_9_eigenvalue_lower_bound (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.PosSemidef) (s : ℕ) (hs0 : 0 < s) (hsn : s < n) :
    ((((1 / 2 : ℝ) * Real.log (∏ i, ((s : ℝ) / n * hC.isHermitian.eigenvalues i ^ 2
        + 1 - (s : ℝ) / n))) : ℝ) : EReal) ≤ linx C s 1 := by sorry

end MaskedLinx
