-- Prove2me | Theorems.Thm_ModularCurve_exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_diamond_cyclotomic_toricOrthogonal_mem_span_degeneracy_inertiaAugmentation_of_dvd_of_not_sq_dvd
-- name    : ModularCurve.exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_diamond_cyclotomic_toricOrthogonal_mem_span_degeneracy_inertiaAugmentation_of_dvd_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/26e91cd1-1d83-5d26-8022-ff02af37d397
-- title:
--   Twisted pairing on Tₚ J₁(M) and orthogonality at p
-- statement:
--   Let $M\ge 1$ and let $p$ be a prime with $p\mid M$ and $p^2\nmid M$. Assume `HeckeDiamondInputsAll M` (for each prime $\ell$ the Hecke input data at level $M$, and for each $d$ coprime to $M$ the existence of a diamond automorphism of the $q$-expansion function field of $X_1(M)$ together with a base-change automorphism over $\overline{\mathbb Q}$), assume `HeckeDiamondCommuteBar M` (the Hecke and diamond endomorphisms of $J_1(M)=\mathrm{Pic}^0$ of the base-changed function field commute pairwise), and assume `DegeneracyPullbackInputs (M/p) M p` (the divisibility, integrality, principal-divisor and fundamental-identity data making the two degeneracy pull-backs from level $M/p$ to level $M$ defined). Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit in $P$, and let $K$ be a field of characteristic zero that is a $\mathbb Z_p$-algebra. With $J_1(M)$ carrying the Hecke-algebra module structure `heckeModuleOneBar M` and $T=T_p J_1(M)$ the $p$-adic Tate module (sequences $x:\mathbb N\to J_1(M)$ with $p^n x_n=0$ and $p\,x_{n+1}=x_n$), the assertion is that there is a $K$-bilinear form $B$ on $V=K\otimes_{\mathbb Z_p}T$ with the following four properties. First, $B$ is non-degenerate on both sides: $B(v,\cdot)=0$ forces $v=0$ and $B(\cdot,w)=0$ forces $w=0$. Second, every element $t$ of `HeckeAlgOne` (the polynomial ring $\mathbb Z[X_\ell,X_d]$ indexed by primes and by natural numbers, acting through `tateHeckeRepOne` base-changed to $K$) is self-adjoint for $B$. Third, for every $\sigma\in\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and every $c\in\mathbb N$ with $\sigma\zeta=\zeta^{c}$ for all $\zeta$ with $\zeta^{M}=1$, and all $v,w\in V$, $B(\sigma v,\sigma\langle c\rangle w)=\chi_p(\sigma)\,B(v,w)$, where $\langle c\rangle$ is the image of `diamondGen c` and $\chi_p(\sigma)\in\mathbb Z_p^\times$ is the $p$-adic cyclotomic character, read in $K$. Fourth, let $x\in T$ be diamond-fixed, meaning that for every level $n$ and every $d\in$ `normFreeRepsAt M p` (the $d<M$ coprime to $M$ with $d\equiv 1 \bmod M/p$) one has $\langle d\rangle x_n=x_n$; suppose $B((1\otimes x),t)=0$ for every $t\in V$ such that $\tau t=\chi_p(\tau)t$ for all $\tau$ in the inertia subgroup of $P$ over $\mathbb Q$ and such that for every $\varphi$ which is a Frobenius at $p$ for $P$ (lying in the decomposition subgroup and acting as the $p$-th power map on the residue field of $P$) both $U_p(\varphi t)=\chi_p(\varphi)t$ and $\varphi(U_p t)=\chi_p(\varphi)t$, where $U_p$ is the image of `heckeGenOne` at $p$. Then there exists $k\in\mathbb N$ with $p^k\cdot x$ in the $\mathbb Z_p$-span of the union of two sets: the set of $z\in T$ such that, for some $i\in\{0,1\}$ and some $w\in T_p J_1(M/p)$, $z_n$ is the image of $w_n$ under the $i$-th degeneracy pull-back `degeneracyPullbackPair (M / p) M p i` for all $n$; and the set of $z$ of the form $\tau y-y$ with $\tau$ in the inertia subgroup of $P$ over $\mathbb Q$ and $y\in T$ diamond-fixed.
--
--   This is the Fricke-twisted Weil pairing on the $p$-adic Tate module of $J_1(M)$, with the self-adjointness of the covariant Hecke and diamond operators and the full Galois law involving the diamond twist, combined with the Grothendieck-style orthogonality computation at a prime $p$ exactly dividing $M$: a diamond-fixed Tate vector orthogonal to the toric conditions at $p$ lies, up to a power of $p$, in the span of the $p$-old classes and the inertia augmentations. It is used in the deduction that the corresponding $p^k$-multiple of the difference between a diamond-twisted Frobenius and the Hecke operator at $p$ lies in that same span, which is the level-lowering input at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_diamond_cyclotomic_toricOrthogonal_mem_span_degeneracy_inertiaAugmentation_of_dvd_of_not_sq_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1DegeneracyPullback
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem ModularCurve.exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_diamond_cyclotomic_toricOrthogonal_mem_span_degeneracy_inertiaAugmentation_of_dvd_of_not_sq_dvd
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M)
    (hIn : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (hdeg : ModularCurve.JOne.DegeneracyPullbackInputs (M / p) M p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K] :
    letI := ModularCurve.heckeModuleOneBar M
    ∃ B : LinearMap.BilinForm K (K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M)),

      (∀ v, (∀ w, B v w = 0) → v = 0) ∧ (∀ w, (∀ v, B v w = 0) → w = 0) ∧

      (∀ (t : ModularCurve.HeckeAlgOne) (v w : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M)),
        B ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) t).baseChange K v) w =
          B v ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) t).baseChange K w)) ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ v w : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M),
          B ((TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange
                K v)
            ((TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange
                K ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) (ModularCurve.diamondGen c)).baseChange
                    K w)) =
            algebraMap ℤ_[p] K
                ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) * B v w) ∧

      (∀ x : TateModule p (ModularCurve.JOne M),
        (∀ (n : ℕ), ∀ d ∈ ModularCurve.normFreeRepsAt M p,
          ModularCurve.diamondOneBar M d ((x : ℕ → ModularCurve.JOne M) n) =
            (x : ℕ → ModularCurve.JOne M) n) →
        (∀ t : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M),
          (∀ τ ∈ P.inertiaSubgroupIn ℚ,
            (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ).baseChange
                K t =
              algebraMap ℤ_[p] K
                  ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • t) →
          (∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt φ p →
            (ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M)
                  (ModularCurve.heckeGenOne ⟨p, Fact.out⟩)).baseChange K
                ((TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
                    φ).baseChange K t) =
              algebraMap ℤ_[p] K
                  ((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • t ∧
            (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) φ).baseChange
                K ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M)
                      (ModularCurve.heckeGenOne ⟨p, Fact.out⟩)).baseChange K t) =
              algebraMap ℤ_[p] K
                  ((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • t) →
          B ((1 : K) ⊗ₜ[ℤ_[p]] x) t = 0) →
        ∃ k : ℕ,
          ((p : ℤ_[p]) ^ k) • x ∈
            Submodule.span ℤ_[p]
              ({z : TateModule p (ModularCurve.JOne M) |
                  ∃ (i : Fin 2) (w : TateModule p (ModularCurve.JOne (M / p))), ∀ n : ℕ,
                    (z : ℕ → ModularCurve.JOne M) n =
                      ModularCurve.JOne.degeneracyPullbackPair (M / p) M p i
                        ((w : ℕ → ModularCurve.JOne (M / p)) n)} ∪
                {z : TateModule p (ModularCurve.JOne M) |
                  ∃ τ ∈ P.inertiaSubgroupIn ℚ, ∃ y : TateModule p (ModularCurve.JOne M),
                    (∀ (n : ℕ), ∀ d ∈ ModularCurve.normFreeRepsAt M p,
                        ModularCurve.diamondOneBar M d ((y : ℕ → ModularCurve.JOne M) n) =
                          (y : ℕ → ModularCurve.JOne M) n) ∧
                      z = TateModule.rep p (ModularCurve.JOne M)
                            (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ y - y})) := by sorry
