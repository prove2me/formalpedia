-- Prove2me | Theorems.Thm_MFHeisGibbs_theorem_2
-- name    : MFHeisGibbs.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:20.753368+00:00
-- url     : https://prove2.me/theorems/0d7328ba-fb87-4037-8756-4a6f4c655cd9
-- title:
--   Theorem 2, (47) — $\mathcal E_C(X)\ge\frac n{n-1}\frac{m_f^4}{54N_f^2}\|X\|_\rho^2$ on $P_n^\perp$
-- statement:
--   Let $\beta\ge0$, let $f$ be continuous with the KMS relation (no normalization) and let $m_f=\inf_{|\nu|\le\beta}|\tilde f(\nu)|$, $N_f=\sup_{|\nu|\le\beta}|f(\nu)|$, with $m_f>0$. For every $n\ge2$ and every $X\in P_n^\perp$,
--
--   $$\mathcal E_C(X)\ge\gamma_f\|X\|_\rho^2,\qquad\gamma_f:=\frac{n}{n-1}\cdot\frac{m_f^4}{54N_f^2}\ge\frac{m_f^4}{54N_f^2},$$
--
--   and consequently $\gamma(\mathcal L_C,P_n^\perp)\ge\gamma_f$. Every eigenvalue of $-\mathcal L_C$ on $P_n^\perp$ is real and at least $\gamma_f$.
--
--   This gives the constant lower bound outside the permutation-invariant sector, which is one half of the high-temperature and critical cases.
--
--   Differences from the source:
--   - encoding: the Dirichlet form and the KMS norm, which are real for these generators → the real part of the complex inner product; reason: Lean's kmsInner is complex-valued
--   - encoding: γ(L, O), 'the smallest eigenvalue of −L on O' (p.8) or the Rayleigh minimum (p.15) → both a Rayleigh clause (sectorGap) and an eigenvalue clause; reason: the page uses the two as equal, and stating both covers each reading
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), Theorem 2, (46), (47), p.15 (PDF 16)

import Definitions.Def_MFHeisGibbs_Generators
import Definitions.Def_MFHeisGibbs_KMS

namespace MFHeisGibbs

/-- **Theorem 2 (Gap bound on the orthogonal complement of the permutation-invariant sector)**,
Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), p.15. For `β ≥ 0`, `f` continuous with the KMS relation (no
normalization), `m_f > 0`, `n ≥ 2`, `X ∈ P_n^⊥`: `E_C(X) ≥ γ_f ∥X∥²_ρ`, `γ_f ≥ m_f⁴/(54 N_f²)`, and
`γ(L_C, P_n^⊥) ≥ γ_f`.

**Formalization Note.** On `P_n^⊥` the page's `γ(L, O)` is "the smallest eigenvalue of `−L` on `O`" (p.8);
both that reading (the eigenvalue clause) and the Rayleigh reading (`sectorGap`, p.15) are stated. -/
theorem theorem_2 (f : ℝ → ℂ) (hf : KMSRel f) (β : ℝ) (hβ : 0 ≤ β) (hm : 0 < mf β f)
    (n : ℕ) (hn : 2 ≤ n) :
    (∀ X ∈ hsPerp (Pn n), gammaF β f n * kmsNormSq β X ≤ dirichlet β (LC β f n) X) ∧
    mf β f ^ 4 / (54 * Nf β f ^ 2) ≤ gammaF β f n ∧
    gammaF β f n ≤ sectorGap β (LC β f n) (hsPerp (Pn n)) ∧
    (∀ (l : ℂ) (X : Op n), X ∈ hsPerp (Pn n) → X ≠ 0 → -(LC β f n X) = l • X →
      l.im = 0 ∧ gammaF β f n ≤ l.re) := by sorry

end MFHeisGibbs
