-- Prove2me | Theorems.Thm_N25_frickeCuspCharacter_psi
-- name    : N25.frickeCuspCharacter_psi
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:03:30.629301+00:00
-- url     : https://prove2.me/theorems/471db752-b179-4d1e-80ba-b2ed33e4c6bc
-- title:
--   The Fricke cusp line realizes the quintic character field
-- statement:
--   Fix $\iota:\overline{\mathbb Q}\hookrightarrow\mathbb C$ and $W=\begin{pmatrix}0&-1\25&0\end{pmatrix}$. Let $t=[p_0-p_1]$ and assume $[p_0-p_2]=6t$, $71t=0$, and $t\ne0$. There exists a geometric field automorphism $w$ satisfying the same Fricke slash compatibility such that
--
--   $$\gamma(w_*t)=57w_*t,\qquad\sigma(w_*t)=\psi(\sigma)w_*t\quad(\sigma\in\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)).$$
--
--   Furthermore $\sigma$ fixes $w_*t$ exactly when $\sigma\in\ker\psi$, the kernel has index five, and the quintic character field is $\mathbb Q$-isomorphic to the fixed field of $\ker\psi$. This identifies the Fricke line with the named quintic character.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_PointDifference
import Theorems.Thm_N25_Endgame_pG25_degree
import Theorems.Thm_ModularCurve_diamondHBar_mul
import Theorems.Thm_ModularCurve_diamondHBar_apply_eq_self_of_mem
import Definitions.Def_N25
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Definitions.Def_N25_CharacterField

set_option autoImplicit false
open scoped MatrixGroups ModularForm
open N25
open AlgebraicCurve N25.Endgame

theorem N25.frickeCuspCharacter_psi
    (ι : Qbar →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (25 : ℝ), 0])
    (hcoeff : pointDiff (pG25 0) (pG25 2)
        ((pG25_degree 0).trans (pG25_degree 2).symm) =
      (6 : ℤ) • pointDiff (pG25 0) (pG25 1)
        ((pG25_degree 0).trans (pG25_degree 1).symm))
    (h71 : (71 : ℤ) • pointDiff (pG25 0) (pG25 1)
        ((pG25_degree 0).trans (pG25_degree 1).symm) = 0)
    (hne : pointDiff (pG25 0) (pG25 1)
        ((pG25_degree 0).trans (pG25_degree 1).symm) ≠ 0) :
    let t : J := pointDiff (pG25 0) (pG25 1)
      ((pG25_degree 0).trans (pG25_degree 1).symm)
    ∃ w : FG ≃ₐ[Qbar] FG,
      (∀ (x : FG) (k : ℤ)
          (f g : ModularForm (CohCarrier.GammaH 25 H25 : Subgroup (GL (Fin 2) ℝ)) k),
        ModularCurve.coeffMap ι (x : LaurentSeries Qbar) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
        ModularCurve.coeffMap ι (w x : LaurentSeries Qbar) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W))) ∧
      gamma (SemilinearAut.ofAlgAut w • t) =
        (57 : ℤ) • (SemilinearAut.ofAlgAut w • t) ∧
      (∀ σ : Gal, σ • (SemilinearAut.ofAlgAut w • t) =
        (psi σ : ZMod 71).val • (SemilinearAut.ofAlgAut w • t)) ∧
      (∀ σ : Gal, σ • (SemilinearAut.ofAlgAut w • t) =
        SemilinearAut.ofAlgAut w • t ↔ σ ∈ psi.ker) ∧
      psi.ker.index = 5 ∧
      Nonempty (characterField ≃ₐ[ℚ] IntermediateField.fixedField psi.ker) := by sorry
