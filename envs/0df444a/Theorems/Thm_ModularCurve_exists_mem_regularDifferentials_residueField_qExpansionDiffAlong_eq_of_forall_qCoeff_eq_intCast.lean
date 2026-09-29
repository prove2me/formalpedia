-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
-- name    : ModularCurve.exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/1c90d028-a5cd-50a4-bf5c-f60d33a5fcea
-- title:
--   Integral weight-two cusp forms give regular differentials mod p
-- statement:
--   Let $p$ be a prime, let $N \ge 1$, and assume $p \nmid N$. Let $A$ be a valuation subring of $\overline{\mathbf{Q}} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense that the image of $p$ is a non-unit of $A$, and write $\kappa =$ `IsLocalRing.ResidueField A`. Let $f$ be a cusp form of weight $2$ for $\Gamma_0(N)$ and let $a : \mathbf{N} \to \mathbf{Z}$ be such that for every $n$ the $n$-th coefficient of the $q$-expansion of $f$ (of width $1$) equals the complex number $a_n$. Let $F =$ `modularFunctionFieldC` $\kappa\, N$ be the intermediate field of the Laurent series field $\kappa((q))$ generated over $\kappa$ by `jqModC` $\kappa$, namely $q^{-1}$ times the reduction in $\kappa$ of the integral power series `jNum`, and by its substitution $q \mapsto q^N$. Then there exists $\omega \in \Omega[F \,/\, \kappa]$ which is regular, i.e. for every place $v$ of $F$ over $\kappa$ — a valuation subring of $F$ containing $\kappa$, not all of $F$, and a principal ideal ring — one may write $\omega = g \cdot \mathrm{d}\pi_v$ with $g$ in the valuation ring of $v$ and $\pi_v$ the chosen uniformiser, and such that the $q$-expansion map `qExpansionDiffAlong` attached to the inclusion $F \hookrightarrow \kappa((q))$ — the $\kappa$-linear map $\varphi$ with $\varphi(\mathrm{d}x) = \theta(x)$ and $\varphi(h\omega) = h\,\varphi(\omega)$, if such a map exists, and $0$ otherwise — sends $\omega$ to the Laurent series $\sum_{n \ge 0} \bar a_n q^n$, where $\bar a_n$ is the image of $a_n$ in $\kappa$.
--
--   This is the good-reduction statement for the differentials $\omega_f = f(q)\,\mathrm{d}q/q$ attached to weight-two cusp forms with rational integral Fourier coefficients: such a differential reduces, at a place of $\overline{\mathbf{Q}}$ above a prime $p$ not dividing the level, to a regular differential on the geometric special fibre of $X_0(N)$, with $q$-expansion the coefficientwise reduction. It is used in the form [`ModularCurve.exists_mem_regularDifferentials_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast`](thm.html#ModularCurve.exists_mem_regularDifferentials_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast), which transfers the conclusion to an arbitrary algebraically closed field of characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open ModularCurve AlgebraicCurve

theorem ModularCurve.exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (a : ℕ → ℤ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    ∃ ω ∈ regularDifferentials (IsLocalRing.ResidueField A)
        (modularFunctionFieldC (IsLocalRing.ResidueField A) N),
      qExpansionDiffAlong (modularFunctionFieldC (IsLocalRing.ResidueField A) N).val ω =
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A)
          (PowerSeries.mk fun n => (a n : IsLocalRing.ResidueField A)) := by sorry
