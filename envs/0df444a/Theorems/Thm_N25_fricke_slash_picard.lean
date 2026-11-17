-- Prove2me | Theorems.Thm_N25_fricke_slash_picard
-- name    : N25.fricke_slash_picard
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:33:53.58714+00:00
-- url     : https://prove2.me/theorems/f6da2d56-6e1d-4bfb-8fd7-26086488151d
-- title:
--   The Fricke slash operator induces an involution on the Picard group
-- statement:
--   Fix an embedding $\iota:\overline{\mathbb Q}\hookrightarrow\mathbb C$ and $W=\begin{pmatrix}0&-1\25&0\end{pmatrix}$. There exists a $\overline{\mathbb Q}$-algebra automorphism $w$ of the geometric level-$25$ function field that transports every modular-form quotient relation through slash by $W$. Its induced action $w_*$ on the Jacobian satisfies
--
--   $$\delta_d\bigl(w_*\delta_d(x)\bigr)=w_*x,\qquad w_*^2x=x,$$
--
--    for all diamond labels $d$ and all $x\in J$; moreover, if $\sigma$ acts on $25$th roots by the power $c$, then $w_*(\sigma x)=\sigma\delta_c(w_*x)$. This establishes the Fricke involution and its diamond and Galois compatibilities.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25
open UpperHalfPlane ModularCurve HahnSeries AlgebraicCurve
open scoped MatrixGroups ModularForm

theorem N25.fricke_slash_picard
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (25 : ℝ), 0]) :
    ∃ w : xHFunctionFieldBar 25 H25 ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar 25 H25,
      (∀ (x : xHFunctionFieldBar 25 H25) (k : ℤ)
          (f g : ModularForm (CohCarrier.GammaH 25 H25 : Subgroup (GL (Fin 2) ℝ)) k),
        coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) *
            ofPowerSeries ℤ ℂ (qExpansion 1 ⇑g) = ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f) →
        coeffMap ι (w x : LaurentSeries (AlgebraicClosure ℚ)) *
            ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] W)) =
          ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] W))) ∧
      (∀ (d : (ZMod 25)ˣ) (x : J),
        diamondHBar 25 H25 d (SemilinearAut.ofAlgAut w • diamondHBar 25 H25 d x) =
          SemilinearAut.ofAlgAut w • x) ∧
      (∀ x : J, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x) ∧
      (∀ (σ : Gal) (c : ℕ) (hc : c.Coprime 25),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ 25 = 1 → σ ζ = ζ ^ c) →
        ∀ x : J, SemilinearAut.ofAlgAut w • (σ • x) =
          σ • diamondHBar 25 H25 (ZMod.unitOfCoprime c hc) (SemilinearAut.ofAlgAut w • x)) := by sorry
