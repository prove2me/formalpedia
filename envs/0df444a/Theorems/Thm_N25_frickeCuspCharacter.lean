-- Prove2me | Theorems.Thm_N25_frickeCuspCharacter
-- name    : N25.frickeCuspCharacter
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:03:15.731171+00:00
-- url     : https://prove2.me/theorems/3e4bf170-df7a-4bef-98eb-9e869b8f1aac
-- title:
--   The Fricke transform of the cusp class has eigenvalue $57$ and the expected Galois character
-- statement:
--   Fix an embedding $\iota:\overline{\mathbb Q}\hookrightarrow\mathbb C$ and a real matrix $W=\begin{pmatrix}0&-1\25&0\end{pmatrix}$. Let $t=[p_0-p_1]\in J$, and assume $[p_0-p_2]=6t$ and $71t=0$. Then there exists a $\overline{\mathbb Q}$-algebra automorphism $w$ of the geometric function field such that slash by $W$ carries every relation $\iota_*(x)q(g)=q(f)$ to the corresponding relation $\iota_*(wx)q(g|_kW)=q(f|_kW)$, the induced action $w_*$ on $J$ is an involution, and
--
--   $$\gamma(w_*t)=57w_*t.$$
--
--   Moreover, if $\sigma$ acts on $25$th roots by $\zeta\mapsto\zeta^c$ and $[c]=2^kh$ with $h\in H_{25}$, then $\sigma(w_*t)=57^kw_*t$. This constructs the Fricke cusp line with its explicit diamond and Galois character.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_PointDifference
import Theorems.Thm_N25_Endgame_pG25_degree
import Theorems.Thm_ModularCurve_diamondHBar_mul
import Theorems.Thm_ModularCurve_diamondHBar_apply_eq_self_of_mem
import Definitions.Def_N25

set_option autoImplicit false
open scoped MatrixGroups ModularForm
open N25
open AlgebraicCurve N25.Endgame

theorem N25.frickeCuspCharacter
    (ι : Qbar →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (25 : ℝ), 0])
    (hcoeff : pointDiff (pG25 0) (pG25 2)
        ((pG25_degree 0).trans (pG25_degree 2).symm) =
      (6 : ℤ) • pointDiff (pG25 0) (pG25 1)
        ((pG25_degree 0).trans (pG25_degree 1).symm))
    (h71 : (71 : ℤ) • pointDiff (pG25 0) (pG25 1)
        ((pG25_degree 0).trans (pG25_degree 1).symm) = 0) :
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
      (∀ x : J, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x) ∧
      gamma (SemilinearAut.ofAlgAut w • t) =
        (57 : ℤ) • (SemilinearAut.ofAlgAut w • t) ∧
      (∀ (σ : Gal) (c : ℕ) (hc : c.Coprime 25) (k : ℕ) (h : H25),
        (∀ ζ : Qbar, ζ ^ 25 = 1 → σ ζ = ζ ^ c) →
        ZMod.unitOfCoprime c hc = (ZMod.unitOfCoprime 2 (by decide)) ^ k * (h : (ZMod 25)ˣ) →
        σ • (SemilinearAut.ofAlgAut w • t) =
          (57 ^ k : ℤ) • (SemilinearAut.ofAlgAut w • t)) := by sorry
