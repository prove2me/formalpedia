-- Prove2me | Theorems.Thm_IsGalois_isMulCoboundary2_of_isPGroup_of_C1
-- name    : IsGalois.isMulCoboundary2_of_isPGroup_of_C1
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-14T05:03:29.321511+00:00
-- url     : https://prove2.me/theorems/2120216e-1f19-41e2-ae7d-9cd9fac3fae9
-- title:
--   Brauer group of a $C_1$ field: $\mathrm{Br}(L/K) = H^2(\mathrm{Gal}(L/K), L^\times) = 0$ for every finite Galois $p$-extension $L/K$
-- statement:
--   Call a field $F$ **$C_1$** if every polynomial $f \in F[x_1, \dots, x_n]$ (for any $n$) whose total degree is smaller than the number of variables, $\deg f < n$, and whose constant term is $0$ has a nontrivial zero:
--
--   $$\exists\, x \in F^n,\ x \ne 0,\ f(x) = 0.$$
--
--   Let $K$ be a $C_1$ field, let $p$ be a prime, and let $L/K$ be a finite Galois extension whose Galois group $G = \mathrm{Gal}(L/K)$ is a $p$-group. Then every multiplicative 2-cocycle $f : G \times G \to L^\times$, i.e.
--
--   $$f(gh, j)\, f(g, h) = g\bigl(f(h, j)\bigr)\, f(g, hj) \qquad (g, h, j \in G),$$
--
--   is a 2-coboundary: there is $x : G \to L^\times$ with
--
--   $$g\bigl(x(h)\bigr)\, x(gh)^{-1}\, x(g) = f(g, h) \qquad (g, h \in G).$$
--
--   Equivalently, the relative Brauer group $\mathrm{Br}(L/K) = H^2(\mathrm{Gal}(L/K), L^\times)$ vanishes.
--
--   Role: this is the $p$-primary part of the theorem that the Brauer group of a $C_1$ field is trivial (Tsen, Lang; Serre, *Local Fields* X.7, *Galois Cohomology* II.3). By Tsen's theorem it applies to every algebraic extension of $k(t)$ with $k$ algebraically closed, i.e. to function fields of curves over $k$, and it is the input for $\mathrm{cd}_p \le 1$ of their Galois groups.
--
--   **Formalization Note**: $\mathrm{Gal}(L/K)$ is `L ≃ₐ[K] L`, acting on $L^\times$ = `Lˣ` by Mathlib's action of $K$-algebra automorphisms on units; the cocycle and coboundary conditions are Mathlib's `groupCohomology.IsMulCocycle₂` and `groupCohomology.IsMulCoboundary₂`, exactly the two displayed identities. The $C_1$ property of $K$ is written out as the hypothesis `hK`: `f.totalDegree < n` and `MvPolynomial.constantCoeff f = 0` imply `∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0` (the strong form of $C_1$, Lang's "quasi-algebraically closed", as in the Proved theorem `RatFunc.tsen_and_lang_C1`). "$G$ is a $p$-group" is `IsPGroup p (L ≃ₐ[K] L)` together with `p.Prime`.
-- source:
--   J.-P. Serre, Local Fields, Graduate Texts in Mathematics 67, Springer 1979, doi:10.1007/978-1-4757-5673-9, Chapter X, Section 7 (Proposition 10); J.-P. Serre, Galois Cohomology, Springer 1997, doi:10.1007/978-3-642-59141-9, Chapter II, Section 3; S. Lang, On quasi algebraic closure, Ann. of Math. (2) 55 (1952), 373-390, doi:10.2307/1969785

import Mathlib

set_option autoImplicit false

theorem IsGalois.isMulCoboundary2_of_isPGroup_of_C1
    (K : Type*) [Field K]
    (hK : ∀ (n : ℕ) (f : MvPolynomial (Fin n) K), f.totalDegree < n → MvPolynomial.constantCoeff f = 0 →
      ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0)
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) (hp : p.Prime) (hG : IsPGroup p (L ≃ₐ[K] L))
    (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (hf : groupCohomology.IsMulCocycle₂ f) :
    groupCohomology.IsMulCoboundary₂ f := by sorry
