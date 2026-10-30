-- Prove2me | Theorems.Thm_KUModComp_psi_subst
-- name    : KUModComp.psi_subst
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:58:39.503743+00:00
-- url     : https://prove2.me/theorems/8bf53d95-83d4-4be6-a0f6-99487d8d4240
-- title:
--   $\psi_{h,\ell}$ inverts the Kronecker substitution
-- statement:
--   Let $R$ be a commutative ring, $h \ge 2$, $\ell \in \mathbb N$, and let $f \in R[X_0,\dots,X_{m-1}]$ have individual degrees at most $h^\ell - 1$. If $g = \psi_{h,\ell}(f)$, then
--   $$
--   f(X_0,\dots,X_{m-1}) = g\bigl(X_0^{h^0}, X_0^{h^1}, \dots, X_0^{h^{\ell-1}}, \dots, X_{m-1}^{h^0}, \dots, X_{m-1}^{h^{\ell-1}}\bigr),
--   $$
--   that is, substituting $Y_{i,j} \mapsto X_i^{h^j}$ into $\psi_{h,\ell}(f)$ returns $f$.
--
--   This is the sense in which $\psi_{h,\ell}$ is the inverse of the Kronecker substitution, and the identity behind the correctness of the reduction in Theorem 3.1.
--
--   Differences from the source:
--   - reading: "write $a$ in base $h$" → hypothesis $2 \le h$; reason: base-$h$ expansion is only defined for $h \ge 2$.
--   - encoding: $g(X_0^{h^0},\dots,X_{m-1}^{h^{\ell-1}})$ → `aeval (fun p => X p.1 ^ (h ^ p.2)) (psi h ℓ f)`; reason: Lean substitution of the variables $Y_{i,j}$ = `X (i, j)`; same instances.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), remark after Definition 2.3, p. 8

import Mathlib
import Definitions.Def_KUModComp_psi

open MvPolynomial

namespace KUModComp

/-- **`ψ_{h,ℓ}` is the inverse of the Kronecker substitution** (Kedlaya–Umans, Dagstuhl 08381
(2008), remark after Definition 2.3, p. 8). Let `h ≥ 2` and let `f ∈ R[X_0, …, X_{m-1}]` have
individual degrees at most `h^ℓ - 1`. If `g = ψ_{h,ℓ}(f)`, then
`f(X_0, …, X_{m-1}) = g(X_0^{h^0}, X_0^{h^1}, …, X_0^{h^{ℓ-1}}, …, X_{m-1}^{h^0}, …, X_{m-1}^{h^{ℓ-1}})`,
i.e. substituting `Y_{i,j} ↦ X_i^{h^j}` into `ψ_{h,ℓ}(f)` gives back `f`. -/
theorem psi_subst {R : Type*} [CommRing R] {m : ℕ} (h ℓ : ℕ) (hh : 2 ≤ h)
    (f : MvPolynomial (Fin m) R) (hf : ∀ i, f.degreeOf i ≤ h ^ ℓ - 1) :
    aeval (fun p : Fin m × Fin ℓ => (X p.1 : MvPolynomial (Fin m) R) ^ (h ^ (p.2 : ℕ)))
      (psi h ℓ f) = f := by sorry

end KUModComp
