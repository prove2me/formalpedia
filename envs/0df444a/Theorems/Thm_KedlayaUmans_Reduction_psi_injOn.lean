-- Prove2me | Theorems.Thm_KedlayaUmans_Reduction_psi_injOn
-- name    : KedlayaUmans.Reduction.psi_injOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:06.08998+00:00
-- url     : https://prove2.me/theorems/ea1a9edc-e9e7-4790-bfa1-31a72d4067a8
-- title:
--   Definition 2.3 — $\psi_{h,\ell}$ is injective on individual degrees at most $h^\ell - 1$
-- statement:
--   Let $R$ be a commutative ring and $h \ge 2$, $\ell \ge 0$. The inverse Kronecker map $\psi_{h,\ell}$ is injective on the set of polynomials in $R[X_0, \dots, X_{m-1}]$ with individual degrees at most $h^\ell - 1$:
--   $$
--   \deg_{X_i} f,\ \deg_{X_i} f' \le h^\ell - 1 \text{ for all } i,\quad \psi_{h,\ell}(f) = \psi_{h,\ell}(f') \;\Longrightarrow\; f = f'.
--   $$
--
--   The paper records this as a remark after Definition 2.3; the proof of Theorem 3.1 does not use it.
--
--   **Formalization Note** Stated with `Set.InjOn` on $\{f \mid \forall i,\ \deg_{X_i} f \le h^\ell - 1\}$.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 8, remark after Definition 2.3

import Mathlib
import Definitions.Def_KedlayaUmans_Reduction_Psi

namespace KedlayaUmans.Reduction

theorem psi_injOn {R : Type*} [CommRing R] {m : ℕ} (h ℓ : ℕ) (hh : 2 ≤ h) :
    Set.InjOn (psi (R := R) (m := m) h ℓ)
      {f : MvPolynomial (Fin m) R | ∀ i, f.degreeOf i ≤ h ^ ℓ - 1} := by sorry

end KedlayaUmans.Reduction
