-- Prove2me | Theorems.Thm_ModularCurve_exists_addEquiv_torsionBy_jZero_periodLattice_quotient_heckeOperatorBar
-- name    : ModularCurve.exists_addEquiv_torsionBy_jZero_periodLattice_quotient_heckeOperatorBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/c1b2765e-7ef5-5198-b279-8c609d534a68
-- title:
--   n-torsion of J₀(N) as Λ_N/nΛ_N, Hecke-equivariantly
-- statement:
--   Let $N\ge 1$ and let $n$ be a natural number with $0<n$. Write $J_0(N)$ for [`ModularCurve.JZero N`](def/ModularCurve_ArithmeticGalois.html#L115), the degree-zero divisor class group $\mathrm{Pic}^0$ of the function field obtained by base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$ inside Laurent series, i.e. degree-zero divisors modulo principal divisors; and write $\Lambda_N\subset S_2(\Gamma_0(N))^\vee$ for [`ModularCurve.periodLattice N`](def/ModularCurve_PeriodLattice.html#L102), the $\mathbb Z$-span of the periods $\mathrm{period}\,N(\gamma)$, $\gamma\in\Gamma_0(N)$, each a $\mathbb C$-linear functional on weight-two cusp forms for $\Gamma_0(N)$ obtained by integration from $i$ to $\gamma\cdot i$. The assertion is that there exists an isomorphism of additive groups $\tau$ from the $n$-torsion submodule $\{x\in J_0(N): n\,x=0\}$ onto the quotient of $\Lambda_N$ by $(n)\cdot\Lambda_N$, which is Hecke-equivariant in the following sense: for every prime $\ell$, all $x,y$ in the $n$-torsion and every $\lambda\in\Lambda_N$, if $y=$ `heckeOperatorBar N ℓ` $x$ in $J_0(N)$ (the $\mathbb Z$-linear endomorphism induced by the total Hecke correspondence at $\ell$ on $\mathrm{Pic}^0$) and $\tau(x)$ is the class of $\lambda$, then $\tau(y)$ is the class of `periodLatticeHeckeEnd N (heckeGen ℓ)` applied to $\lambda$, where the latter is the value at the polynomial generator $X_\ell$ of the Hecke algebra $\mathbb Z[X_\ell:\ell\text{ prime}]$ of the ring homomorphism into $\mathrm{End}_{\mathbb Z}(\Lambda_N)$ given, when $\Lambda_N$ is stable under the dual Hecke action, by restricting that action to $\Lambda_N$.
--
--   This is the reduction modulo $n$ of the analytic uniformisation $J_0(N)(\mathbb C)\cong S_2(\Gamma_0(N))^\vee/\Lambda_N$, giving the classical identification of $J_0(N)[n]$ with $\Lambda_N/n\Lambda_N$ (equivalently with $H_1(X_0(N),\mathbb Z/n)$) compatibly with the Hecke operators. It is used to transport homological constructions with Hecke action into the $n$-torsion of the Jacobian, in the comparison of parabolic homomorphisms with torsion points of $J_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_addEquiv_torsionBy_jZero_periodLattice_quotient_heckeOperatorBar.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_addEquiv_torsionBy_jZero_periodLattice_quotient_heckeOperatorBar
    (N : ℕ) [NeZero N] (n : ℕ) (hn : 0 < n) :
    ∃ τ : ↥(Submodule.torsionBy ℤ (ModularCurve.JZero N) (n : ℤ)) ≃+
        (↥(ModularCurve.periodLattice N) ⧸
          (Ideal.span {(n : ℤ)} • (⊤ : Submodule ℤ ↥(ModularCurve.periodLattice N)))),
      ∀ (ℓ : Nat.Primes) (x y : ↥(Submodule.torsionBy ℤ (ModularCurve.JZero N) (n : ℤ)))
        (lam : ↥(ModularCurve.periodLattice N)),
        (y : ModularCurve.JZero N) = ModularCurve.heckeOperatorBar N ℓ (x : ModularCurve.JZero N) →
        τ x = Submodule.Quotient.mk lam →
        τ y = Submodule.Quotient.mk (ModularCurve.periodLatticeHeckeEnd N (ModularCurve.heckeGen ℓ) lam) := by sorry
