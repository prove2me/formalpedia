-- Prove2me | Theorems.Thm_KUModComp_correctness_congr
-- name    : KUModComp.correctness_congr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:59:48.835621+00:00
-- url     : https://prove2.me/theorems/cfc9664c-8370-4b6b-ab6e-2689021dd1c9
-- title:
--   Correctness of the reduction: $f'(g_{0,0},\dots,g_{m-1,\ell-1}) \equiv f(g_0,\dots,g_{m-1}) \pmod h$
-- statement:
--   Let $R$ be a commutative ring, $d_0 \ge 2$, $d \in \mathbb N$, $\ell = \lceil \log_{d_0} d \rceil$, and let $f \in R[X_0,\dots,X_{m-1}]$ have individual degrees at most $d-1$. Let $g_0,\dots,g_{m-1} \in R[X]$ and let $h \in R[X]$ have a unit leading coefficient. Put $f' = \psi_{d_0,\ell}(f)$ and
--   $$
--   g_{i,j}(X) = g_i(X)^{d_0^{\,j}} \bmod h(X), \qquad i < m,\ j < \ell .
--   $$
--   Then
--   $$
--   f'\bigl(g_{0,0}(X),\dots,g_{m-1,\ell-1}(X)\bigr) \equiv f\bigl(g_0(X),\dots,g_{m-1}(X)\bigr) \pmod{h(X)} .
--   $$
--
--   This is the observation from which the correctness of the algorithm of Theorem 3.1 follows.
--
--   Differences from the source:
--   - encoding: congruence modulo $h$ → equality of the remainders `modU · h u`, i.e. remainders on division by the monic associate $u^{-1}h$; reason: two polynomials are congruent modulo $h$ iff their remainders by $u^{-1}h$ agree; same instances.
--   - encoding: $\ell = \lceil \log_{d_0} d \rceil$ → `Nat.clog d₀ d`; reason: equal for $d_0 \ge 2$, $d \ge 1$.
--   - generalization: $d_0 < d$, $\deg g_i, \deg h \le N - 1$ → no condition $d_0 < d$, $g_i$ and $h$ of any degree; reason: the congruence holds without them (also for $d \le 1$, where the Lean hypothesis `degreeOf ≤ d - 1 = 0` admits every constant $f$, not only the page's $f = 0$ at $d = 0$); specializes to the source's data.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), proof of Theorem 3.1, steps 1–2 (p. 9) and the correctness sentence (p. 10)

import Mathlib
import Definitions.Def_KUModComp_psi
import Definitions.Def_KUModComp_modCompSpec

open Polynomial

namespace KUModComp

/-- **Correctness of the reduction** (Kedlaya–Umans, Dagstuhl 08381 (2008), proof of Theorem 3.1,
p. 10). Let `d_0 ≥ 2`, `ℓ = ⌈log_{d_0} d⌉` (`Nat.clog d₀ d`), `f ∈ R[X_0, …, X_{m-1}]` with
individual degrees at most `d - 1`, `g_0, …, g_{m-1} ∈ R[X]`, and `h ∈ R[X]` whose leading
coefficient is a unit `u`. With `f' = ψ_{d_0,ℓ}(f)` and `g_{i,j} = g_i^{d_0^j} mod h`,
`f'(g_{0,0}, …, g_{m-1,ℓ-1}) ≡ f(g_0, …, g_{m-1}) (mod h)`,
stated as equality of the remainders modulo `h` (`modU`, remainder by the monic associate of `h`). -/
theorem correctness_congr {R : Type*} [CommRing R] {m : ℕ} (d d₀ : ℕ) (hd₀ : 2 ≤ d₀)
    (f : MvPolynomial (Fin m) R) (hf : ∀ i, f.degreeOf i ≤ d - 1)
    (g : Fin m → R[X]) (hp : R[X]) (u : Rˣ) (hu : hp.leadingCoeff = (u : R)) :
    modU (MvPolynomial.aeval
        (fun p : Fin m × Fin (Nat.clog d₀ d) => modU (g p.1 ^ (d₀ ^ (p.2 : ℕ))) hp u)
        (psi d₀ (Nat.clog d₀ d) f)) hp u
      = modU (MvPolynomial.aeval g f) hp u := by sorry

end KUModComp
