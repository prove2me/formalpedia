-- Prove2me | Theorems.Thm_ModularCurve_rep_diamondGen_apply_inertia_sub_eq_of_nsmul_sub_sum_tateModule_jOne_of_dvd_of_not_sq_dvd_of_le_div
-- name    : ModularCurve.rep_diamondGen_apply_inertia_sub_eq_of_nsmul_sub_sum_tateModule_jOne_of_dvd_of_not_sq_dvd_of_le_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/bde50c4c-8077-596e-ae81-3701802a420a
-- title:
--   Inertia relation (⟨ u⟩σ-1)(σ-1)=0 on norm-free vectors
-- statement:
--   Let $M$ be a nonzero natural number, $p$ a prime and $q$ a prime with $q\mid M$, $q^2\nmid M$, $5\le M/q$ and $p\ne q$. Assume [`ModularCurve.HeckeDiamondCommuteBar M`](def/ModularCurve_X1HeckeModule.html#L54), i.e. the endomorphisms of $J_1(M)$ given by the Hecke operators (indexed by primes) and the diamond operators (indexed by naturals) commute pairwise; here $J_1(M)$ is [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186), the degree-zero divisor class group of the function field of $X_1(M)$ base changed to $\overline{\mathbb Q}$, and the commutation hypothesis makes [`ModularCurve.heckeModuleOneBar M`](def/ModularCurve_X1HeckeModule.html#L129) the module structure over `HeckeAlgOne` $=\mathbb Z[X_i : i\in\mathrm{Primes}\sqcup\mathbb N]$ obtained by evaluating the generators at those endomorphisms, `diamondGen d` being the variable indexed by $d\in\mathbb N$. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $P$, and let $\sigma$ be a $\mathbb Q$-automorphism of $\overline{\mathbb Q}$ lying in the inertia subgroup at $P$ (the image in $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ of the inertia subgroup inside the decomposition subgroup). Let $u\in\mathbb N$ satisfy $u\equiv 1 \pmod{M/q}$ and suppose $\sigma\zeta=\zeta^u$ for every $\zeta\in\overline{\mathbb Q}$ with $\zeta^q=1$. Let $x,y$ lie in the $p$-adic Tate module [`TateModule p (JOne M)`](def/EllipticCurve_TateModule.html#L15), the group of sequences $(z_n)$ in $J_1(M)$ with $p^nz_n=0$ and $pz_{n+1}=z_n$, on which both $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ and `HeckeAlgOne` act termwise through [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174), and suppose $y=\#\Delta\cdot x-\sum_{d\in\Delta}\langle d\rangle x$, where $\Delta$ is the set of $d<M$ with $\gcd(d,M)=1$ and $d\equiv 1\pmod{M/q}$. Then $\langle u\rangle\,\sigma\,(\sigma y-y)=\sigma y-y$, that is, $(\langle u\rangle\sigma-1)(\sigma-1)y=0$.
--
--   This is the local behaviour at a prime $q$ exactly dividing the level, in the form going back to Deligne–Rapoport and Langlands: on the part of the $p$-adic Tate module of $J_1(M)$ killed by the norm from level $M/q$, the operator $(\langle u\rangle\sigma-1)(\sigma-1)$ vanishes for inertia elements $\sigma$ at $q$ acting on $\mu_q$ by $u$-th powers. It feeds the construction of the $p$-adic Galois representation attached to a Hecke eigenclass together with the prescribed relations between Frobenius and inertia at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_rep_diamondGen_apply_inertia_sub_eq_of_nsmul_sub_sum_tateModule_jOne_of_dvd_of_not_sq_dvd_of_le_div.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.rep_diamondGen_apply_inertia_sub_eq_of_nsmul_sub_sum_tateModule_jOne_of_dvd_of_not_sq_dvd_of_le_div
    (M q p : ℕ) [NeZero M] [Fact p.Prime] (hq : q.Prime) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ M) (hMq : 5 ≤ M / q) (hpq : p ≠ q)
    (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ)
    (u : ℕ) (hu : u ≡ 1 [MOD M / q])
    (hcyc : ∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ u)
    (x y : TateModule p (ModularCurve.JOne M))
    (hy : letI := ModularCurve.heckeModuleOneBar M
      y = ((Finset.range M).filter
              (fun d => Nat.Coprime d M ∧ d ≡ 1 [MOD M / q])).card • x
          - ∑ d ∈ (Finset.range M).filter
              (fun d => Nat.Coprime d M ∧ d ≡ 1 [MOD M / q]),
              TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne
                (ModularCurve.diamondGen d) x) :
    letI := ModularCurve.heckeModuleOneBar M
    TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne
        (ModularCurve.diamondGen u)
        (TateModule.rep p (ModularCurve.JOne M)
            (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
          (TateModule.rep p (ModularCurve.JOne M)
              (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ y - y))
      = TateModule.rep p (ModularCurve.JOne M)
            (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ y - y := by sorry
