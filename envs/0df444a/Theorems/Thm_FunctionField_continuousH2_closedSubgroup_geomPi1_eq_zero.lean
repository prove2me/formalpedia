-- Prove2me | Theorems.Thm_FunctionField_continuousH2_closedSubgroup_geomPi1_eq_zero
-- name    : FunctionField.continuousH2_closedSubgroup_geomPi1_eq_zero
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T06:22:15.760511+00:00
-- url     : https://prove2.me/theorems/da89f0f2-16ff-5bb4-858f-edb2d442e969
-- title:
--   $\mathrm{cd}_\ell\,\pi_1(\bar U)\le1$ for an affine curve $U$ over $\mathbb F_q$: $H^2(\Delta,M)=0$ for closed $\Delta\subseteq\pi_1(\bar U)$ and finite $\ell$-primary $M$
-- statement:
--   Let $\mathbb F_q$ be a finite field, $q=p^e$, and let $F$ be a function field over $\mathbb F_q$ (a finite separable extension of $\mathbb F_q(t)$). Let $A\subset F$ be the integral closure of $\mathbb F_q[t]$, so that $U=\operatorname{Spec}A$ is the smooth affine curve obtained from the complete curve of $F$ by removing the places over $t=\infty$. Fix an algebraic closure $\overline F$ and let $K_U\subset\overline F$ be the compositum of all finite Galois extensions $L/F$ in $\overline F$ that are unramified over $A$: for every prime $\mathfrak P$ of the integral closure $A_L$ of $A$ in $L$, the only $g\in\mathrm{Gal}(L/F)$ with $g(b)\equiv b\pmod{\mathfrak P}$ for all $b\in A_L$ is $g=1$. Thus $\mathrm{Gal}(K_U/F)$ with its Krull topology is $\pi_1(U)$, and
--   $$\Gamma=\{g\in\mathrm{Gal}(K_U/F):\ g(x)=x\text{ for every }x\in K_U\text{ with }x^{q^k}=x\text{ for some }k\ge1\}=\mathrm{Gal}(K_U/K_U\cap F\overline{\mathbb F}_q)$$
--   is the geometric fundamental group $\pi_1(\bar U)$ (of a geometric component of $U$ if the constant field of $F$ is larger than $\mathbb F_q$).
--
--   Let $\ell$ be a prime not dividing $q$, $n\ge0$, $\Lambda$ a commutative ring and $M$ a finite $\Lambda$-module with $\ell^nM=0$, carrying a continuous $\Lambda$-linear action $\rho$ of $\mathrm{Gal}(K_U/F)$ (the kernel of $\rho$ is open). Then for every closed subgroup $\Delta\subseteq\Gamma$ of $\mathrm{Gal}(K_U/F)$, $H^2(\Delta,M)=0$ in continuous cochains: every locally constant $f:\Delta\times\Delta\to M$ satisfying the $2$-cocycle identity
--   $$f(gh,j)+f(g,h)=\rho(g)\,f(h,j)+f(g,hj)\qquad(g,h,j\in\Delta)$$
--   is a coboundary: there is a locally constant $b:\Delta\to M$ with $f(g,h)=\rho(g)\,b(h)-b(gh)+b(g)$ for all $g,h\in\Delta$.
--
--   Role: this is the statement $\mathrm{cd}_\ell\,\pi_1(\bar U)\le1$ (the étale cohomological dimension of an affine curve over an algebraically closed field is at most $1$ for $\ell\ne p$). With $\Delta=\Gamma$ it says $H^2(\pi_1(\bar U),M)=0$; with $\Delta$ an $\ell$-Sylow subgroup of $\Gamma$ and $M=\mathbb Z/\ell$ with trivial action it gives $H^2(\Delta,\mathbb Z/\ell)=0$, hence $\mathrm{cd}_\ell\Gamma=\mathrm{cd}_\ell\Delta\le1$ by Serre's criterion for pro-$\ell$ groups.
--
--   **Formalization Note**: $\mathbb F_q$ is `Fq` and $F$ is a `FunctionField Fq F` with the algebra structures over `Polynomial Fq` and `RatFunc Fq` compatible (`IsScalarTower`) and $F/\mathbb F_q(t)$ separable; $A$ is `FunctionField.ringOfIntegers Fq F`. $K_U$ is `KU : IntermediateField F (AlgebraicClosure F)`, fixed by the equation `hKU`: the supremum of the finite-dimensional Galois intermediate fields `L` whose inertia groups at all primes `P` of `integralClosure (FunctionField.ringOfIntegers Fq F) L` are trivial (the congruence $g(b)\equiv b\pmod{\mathfrak P}$ is written `∃ c ∈ P, (c : L) = g b - b`). $\mathrm{Gal}(K_U/F)$ is `KU ≃ₐ[F] KU` with Mathlib's Krull topology. $\Delta$ is a `Subgroup (KU ≃ₐ[F] KU)` that is closed (`hΔc`), and `hΔ` says that every element of $\Delta$ fixes every `x : KU` with `x ^ (Fintype.card Fq) ^ k = x` for some `k > 0`, i.e. $\Delta\subseteq\Gamma$. $\ell\nmid q$ is `¬ l ∣ Fintype.card Fq`. The action is `ρ : Representation Λ (KU ≃ₐ[F] KU) M` with `IsOpen ρ.ker`, $M$ is `Finite` with `(l ^ n) • m = 0` for all `m`; $\Delta$ and $\Delta\times\Delta$ carry the subspace and product topologies, and continuity of cochains with values in the finite discrete module $M$ is `IsLocallyConstant`. The hypotheses are satisfiable and the conclusion is not vacuous: for example $F=\mathbb F_q(t)$ ($U=\mathbb A^1$), $\Delta=\Gamma$ (a closed subgroup), $\ell\ne p$ and $\Lambda=M=\mathbb Z/\ell$ with the trivial action; there the statement is $H^2(\pi_1(\mathbb A^1_{\overline{\mathbb F}_q}),\mathbb Z/\ell)=0$.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Théorie des topos et cohomologie étale des schémas (SGA 4), Tome 3, Lecture Notes in Math. 305, Springer (1973), Exposé X, §5 (cohomological dimension of curves); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1; J.-P. Serre, Galois Cohomology, Springer (1997), Chapter I, §3-4 and Chapter II, §3

import Mathlib

set_option autoImplicit false

theorem FunctionField.continuousH2_closedSubgroup_geomPi1_eq_zero
    (Fq : Type) [Field Fq] [Fintype Fq]
    (F : Type) [Field F] [Algebra Fq F] [Algebra (Polynomial Fq) F] [Algebra (RatFunc Fq) F]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) F] [IsScalarTower Fq (Polynomial Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]
    (l : ℕ) [Fact l.Prime] (hl : ¬ l ∣ Fintype.card Fq)
    (KU : IntermediateField F (AlgebraicClosure F))
    (hKU : KU = ⨆ L : {L : IntermediateField F (AlgebraicClosure F) //
        FiniteDimensional F L ∧ IsGalois F L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) L), P.IsPrime →
          ∀ g : L ≃ₐ[F] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) L, ∃ c ∈ P, (c : L) = g b - b) →
              g = 1}, L.1)
    (Δ : Subgroup (KU ≃ₐ[F] KU)) (hΔc : IsClosed (Δ : Set (KU ≃ₐ[F] KU)))
    (hΔ : ∀ g ∈ Δ, ∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) → g x = x)
    (Λ : Type) [CommRing Λ] (M : Type) [AddCommGroup M] [Module Λ M] [Finite M]
    (ρ : Representation Λ (KU ≃ₐ[F] KU) M) (hρ : IsOpen (ρ.ker : Set (KU ≃ₐ[F] KU)))
    (n : ℕ) (hM : ∀ m : M, (l ^ n) • m = 0)
    (f : Δ × Δ → M) (hf : IsLocallyConstant f)
    (hc : ∀ g h j : Δ, f (g * h, j) + f (g, h) = ρ g (f (h, j)) + f (g, h * j)) :
    ∃ b : Δ → M, IsLocallyConstant b ∧ ∀ g h : Δ, f (g, h) = ρ g (b h) - b (g * h) + b g := by
  sorry
