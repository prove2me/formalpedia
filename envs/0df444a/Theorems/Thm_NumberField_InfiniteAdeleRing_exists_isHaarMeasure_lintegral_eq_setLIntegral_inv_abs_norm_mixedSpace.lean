-- Prove2me | Theorems.Thm_NumberField_InfiniteAdeleRing_exists_isHaarMeasure_lintegral_eq_setLIntegral_inv_abs_norm_mixedSpace
-- name    : NumberField.InfiniteAdeleRing.exists_isHaarMeasure_lintegral_eq_setLIntegral_inv_abs_norm_mixedSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/6a16112a-b4a0-5928-87c2-37bbabc528a5
-- title:
--   Haar measure on GLₙ of the infinite adeles via |N|⁻¹ dX
-- statement:
--   Let $n$ be a finite index type and $K$ a number field, and equip $\mathrm{GL}_n$ of the infinite adele ring $K_\infty =$ `InfiniteAdeleRing K` with a measurable space structure which is the Borel structure of its topology. Write $\mathrm{mixedSpace}\,K = \prod_{w\ \mathrm{real}}\mathbb R \times \prod_{w\ \mathrm{complex}}\mathbb C$ and let `ringEquiv_mixedSpace K` be the canonical ring isomorphism $K_\infty \cong \mathrm{mixedSpace}\,K$. Put $U$ for the set of entry families $e : n \to n \to \mathrm{mixedSpace}\,K$ whose associated matrix is a unit of $M_n(\mathrm{mixedSpace}\,K)$, and $\rho(e) = |N(e)|^{-1}$ in $[0,\infty]$, where $N$ is the algebra norm over $\mathbb R$ of the matrix of $e$, i.e. the determinant of left multiplication by it on the finite-dimensional real algebra $M_n(\mathrm{mixedSpace}\,K)$. Let $\Phi$ send $g \in \mathrm{GL}_n(K_\infty)$ to its entries read in $\mathrm{mixedSpace}\,K$, and let $\Psi$ send $e$ to the invertible matrix obtained by transporting a unit witness back along the inverse isomorphism, and to $1$ when $e \notin U$. The assertion is: $\rho$ is continuous on $U$ and strictly positive there; $\Phi g \in U$ and $\Psi(\Phi g) = g$ for all $g$; and there exists a left Haar measure $\mu$ on $\mathrm{GL}_n(K_\infty)$, regular, with $\int^- f \,d\mu = \int^-_{e \in U} f(\Psi e)\,\rho(e)\,d\mathrm{volume}$ for every measurable $f : \mathrm{GL}_n(K_\infty) \to [0,\infty]$, the outer integral being against the Lebesgue measure of the real vector space $n \to n \to \mathrm{mixedSpace}\,K$.
--
--   This is the classical description of Haar measure on the unit group of a finite-dimensional real algebra $A$, namely $d^\times X = |N_{A/\mathbb R}(X)|^{-1}\,dX$, applied to $A = M_n(K_\infty)$; for $A = M_n(\mathbb R)$ it specialises to $|\det X|^{-n}\,dX$. It packages the measure together with the explicit Lebesgue-coordinate chart $(\Phi,\Psi)$ and the density $\rho$, and is used in the archimedean integral estimates for automorphic forms, through [`AutomorphicForm.exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le`](thm.html#AutomorphicForm.exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfiniteAdeleRing_exists_isHaarMeasure_lintegral_eq_setLIntegral_inv_abs_norm_mixedSpace.lean

import Mathlib.RingTheory.Norm.Defs
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfiniteAdeleRing NumberField.mixedEmbedding
open scoped Classical ENNReal

theorem NumberField.InfiniteAdeleRing.exists_isHaarMeasure_lintegral_eq_setLIntegral_inv_abs_norm_mixedSpace
    (n : Type) [Fintype n] [DecidableEq n] (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL n (InfiniteAdeleRing K))] [BorelSpace (GL n (InfiniteAdeleRing K))] :
    let U : Set (n → n → mixedSpace K) := {e | IsUnit (Matrix.of e)}
    let ρ : (n → n → mixedSpace K) → ℝ≥0∞ := fun e => ENNReal.ofReal |Algebra.norm ℝ (Matrix.of e)|⁻¹
    let Φ : GL n (InfiniteAdeleRing K) → (n → n → mixedSpace K) := fun g i j =>
      ringEquiv_mixedSpace K ((g : Matrix n n (InfiniteAdeleRing K)) i j)
    let Ψ : (n → n → mixedSpace K) → GL n (InfiniteAdeleRing K) := fun e =>
      if h : IsUnit (Matrix.of e) then (h.map (ringEquiv_mixedSpace K).symm.mapMatrix).unit else 1
    ContinuousOn ρ U ∧ (∀ e ∈ U, 0 < ρ e) ∧ (∀ g, Φ g ∈ U) ∧ (∀ g, Ψ (Φ g) = g) ∧
      ∃ μ : Measure (GL n (InfiniteAdeleRing K)), μ.IsHaarMeasure ∧ μ.Regular ∧
        ∀ f : GL n (InfiniteAdeleRing K) → ℝ≥0∞, Measurable f →
          ∫⁻ g, f g ∂μ = ∫⁻ e in U, f (Ψ e) * ρ e ∂volume := by sorry
