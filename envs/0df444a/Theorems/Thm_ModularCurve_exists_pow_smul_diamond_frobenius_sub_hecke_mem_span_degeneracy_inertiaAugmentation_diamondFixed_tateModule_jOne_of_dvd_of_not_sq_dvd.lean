-- Prove2me | Theorems.Thm_ModularCurve_exists_pow_smul_diamond_frobenius_sub_hecke_mem_span_degeneracy_inertiaAugmentation_diamondFixed_tateModule_jOne_of_dvd_of_not_sq_dvd
-- name    : ModularCurve.exists_pow_smul_diamond_frobenius_sub_hecke_mem_span_degeneracy_inertiaAugmentation_diamondFixed_tateModule_jOne_of_dvd_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/ca42922a-9f9c-521d-ba7e-274680644ef4
-- title:
--   Frobenius versus Uₚ on diamond-fixed TₚJ₁(M), p‖ M
-- statement:
--   Let $M\ge 1$ and let $p$ be a prime with $p\mid M$ but $p^2\nmid M$. Assume the project's input hypotheses at level $M$: `HeckeDiamondInputsAll M` (Hecke inputs at every prime $\ell$ for $X_1(M)$ over $\overline{\mathbb Q}$, and, for every $d$ coprime to $M$, a diamond automorphism of the function field of $X_1(M)$ together with its base change to $\overline{\mathbb Q}$), `HeckeDiamondCommuteBar M` (the Hecke and diamond generators commute in their action), and [`ModularCurve.JOne.DegeneracyPullbackInputs (M / p) M p`](def/ModularCurve_X1DegeneracyPullback.html#L109) (the divisibility, integrality, principal-divisor and fundamental-identity data making both degeneracy pull-backs $J_1(M/p)\to J_1(M)$ defined). Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $P$, and let $\sigma$ be a $\mathbb Q$-algebra automorphism of $\overline{\mathbb Q}$ lying in the decomposition subgroup of $P$ and acting on the residue field of $P$ by $x\mapsto x^p$. Let $u$ be a natural number coprime to $M$ with $u\equiv p \pmod{M/p}$. Let $x$ be an element of the Tate module $T_p J_1(M)$, i.e. a sequence $(x_n)$ in $J_1(M)=\mathrm{Pic}^0$ of the base-changed function field, with $p^n x_n=0$ and $p\,x_{n+1}=x_n$, and suppose every $x_n$ is fixed by the diamond operator $\langle d\rangle$ for each $d$ in `normFreeRepsAt M p`, the set of $d<M$ coprime to $M$ with $d\equiv 1\pmod{M/p}$. Then, for the Hecke-algebra module structure `heckeModuleOneBar M` on $J_1(M)$, there exists $k\in\mathbb N$ such that $p^k$ times $\langle u\rangle(\sigma x) - T_p x$ (the Hecke generator at $p$ applied to $x$, subtracted from the diamond generator at $u$ applied to the Galois translate $\sigma x$) lies in the $\mathbb Z_p$-span of the union of two subsets of $T_pJ_1(M)$: those sequences obtained levelwise by applying one of the two degeneracy pull-backs `degeneracyPullbackPair (M / p) M p i`, $i\in\{0,1\}$, to a Tate module element of $J_1(M/p)$; and those of the form $\tau y - y$ with $\tau$ in the inertia subgroup of $P$ over $\mathbb Q$ and $y$ a diamond-fixed element of $T_pJ_1(M)$ in the same sense as $x$.
--
--   This is the geometric input to the local description at $p$ of the Galois representation on the $p$-new, inertia-unramified part of the diamond-fixed Tate module of $J_1(M)$ when $p$ exactly divides $M$: Frobenius agrees with $U_p$ up to the diamond operator at $p$ modulo $M/p$, modulo the $p$-old classes coming from level $M/p$ and modulo the augmentation by inertia, and after clearing a bounded power of $p$. It is used in the passage to the corresponding statement on the unramified quotient of $T_pJ_1(M)$, which feeds the identification of $\mathrm{Frob}_p$ with the $U_p$-eigenvalue for weight-two forms of level exactly divisible by $p$ whose character is unramified at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pow_smul_diamond_frobenius_sub_hecke_mem_span_degeneracy_inertiaAugmentation_diamondFixed_tateModule_jOne_of_dvd_of_not_sq_dvd.lean

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

theorem ModularCurve.exists_pow_smul_diamond_frobenius_sub_hecke_mem_span_degeneracy_inertiaAugmentation_diamondFixed_tateModule_jOne_of_dvd_of_not_sq_dvd
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M)
    (hIn : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (hdeg : ModularCurve.JOne.DegeneracyPullbackInputs (M / p) M p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : P.IsFrobeniusAt σ p)
    (u : ℕ) (hu : Nat.Coprime u M) (hup : u ≡ p [MOD M / p])
    (x : TateModule p (ModularCurve.JOne M))
    (hx : ∀ (n : ℕ), ∀ d ∈ ModularCurve.normFreeRepsAt M p,
      ModularCurve.diamondOneBar M d ((x : ℕ → ModularCurve.JOne M) n) =
        (x : ℕ → ModularCurve.JOne M) n) :
    letI := ModularCurve.heckeModuleOneBar M
    ∃ k : ℕ,
      ((p : ℤ_[p]) ^ k) •
          (ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) (ModularCurve.diamondGen u)
              (TateModule.rep p (ModularCurve.JOne M)
                (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x) -
            ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M)
              (ModularCurve.heckeGenOne ⟨p, Fact.out⟩) x) ∈
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
                        (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ y - y}) := by sorry
