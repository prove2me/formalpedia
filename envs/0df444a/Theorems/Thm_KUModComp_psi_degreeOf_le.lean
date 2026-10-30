-- Prove2me | Theorems.Thm_KUModComp_psi_degreeOf_le
-- name    : KUModComp.psi_degreeOf_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:59:09.388665+00:00
-- url     : https://prove2.me/theorems/f432b5af-4ff0-4cbf-addd-fb7e07871bf0
-- title:
--   $\psi_{d_0,\ell}(f)$ is an MME instance with parameters $d_0$ and $\ell m$
-- statement:
--   Let $R$ be a commutative ring, $d_0 \ge 2$, $\ell \in \mathbb N$ and $f \in R[X_0,\dots,X_{m-1}]$. Then $f' = \psi_{d_0,\ell}(f)$ is a polynomial in the $\ell m$ variables $Y_{i,j}$ ($i<m$, $j<\ell$) with individual degrees at most $d_0 - 1$:
--   $$
--   \deg_{Y_{i,j}} \psi_{d_0,\ell}(f) \le d_0 - 1 \quad\text{for all } i, j, \qquad \#\{Y_{i,j}\} = \ell m .
--   $$
--   So evaluating $f'$ at points is an instance of MULTIVARIATE MULTIPOINT EVALUATION with parameters $d_0$ and $\ell m$; this is step 4 of the proof of Theorem 3.1.
--
--   Differences from the source:
--   - generalization: $f$ with individual degrees at most $d-1$, $\ell = \lceil \log_{d_0} d \rceil$ → every $f$ and every $\ell$; reason: base-$d_0$ digits are at most $d_0 - 1$ for every exponent; specializes to the source's $f$ and $\ell$.
--   - reading: "parameters $d_0, \ell m, N'$" → individual degree bound $d_0 - 1$ and $\ell m$ variables; reason: $N'$ is the number of points chosen in step 3 and says nothing about $f'$; the goal theorem pins all three parameters of the oracle call.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), proof of Theorem 3.1, step 4 and its cost paragraph, p. 10

import Mathlib
import Definitions.Def_KUModComp_psi

open MvPolynomial

namespace KUModComp

/-- **Step 4 of the proof of Theorem 3.1: `ψ_{d_0,ℓ}(f)` is an instance of MULTIVARIATE MULTIPOINT
EVALUATION with parameters `d_0` and `ℓm`** (Kedlaya–Umans, Dagstuhl 08381 (2008), proof of
Theorem 3.1, p. 10). For `d_0 ≥ 2`, every `ℓ`, and every `f ∈ R[X_0, …, X_{m-1}]`, the polynomial
`ψ_{d_0,ℓ}(f)` has individual degree at most `d_0 - 1` in each of its variables `Y_{i,j}`, and it
has `ℓ m` variables. -/
theorem psi_degreeOf_le {R : Type*} [CommRing R] {m : ℕ} (d₀ ℓ : ℕ) (hd₀ : 2 ≤ d₀)
    (f : MvPolynomial (Fin m) R) :
    (∀ p : Fin m × Fin ℓ, (psi d₀ ℓ f).degreeOf p ≤ d₀ - 1) ∧
      Fintype.card (Fin m × Fin ℓ) = ℓ * m := by sorry

end KUModComp
