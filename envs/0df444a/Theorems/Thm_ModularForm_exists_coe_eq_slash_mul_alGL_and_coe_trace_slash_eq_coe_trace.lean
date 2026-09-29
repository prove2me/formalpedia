-- Prove2me | Theorems.Thm_ModularForm_exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace
-- name    : ModularForm.exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/e8fbbe22-ac69-50dd-9e4f-14aacdf57e84
-- title:
--   Trace intertwines twisted Atkin–Lehner with Fricke involution
-- statement:
--   Let $p$ and $M$ be nonzero naturals with $p \mid M$ and $M/p$ nonzero, and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit $u$ with trivial image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$. Write $\Gamma_H(M)$ for the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of the matrices of $\Gamma_0(M)$ whose lower-right entry reduces mod $M$ into $H$, viewed inside $\mathrm{GL}_2(\mathbb{R})$, and likewise $\Gamma_{H'}(M/p)$ for $H'$ the image of $H$; it is assumed that the former has finite relative index in the latter. Let `Wd` be an Atkin–Lehner datum for $M$ and $q = M/p$, i.e. integers $R, a, b$ with $M = qR$ and $qa - Rb = 1$, and let `Wd.alGL` be the associated integral matrix, of determinant $q$, regarded in $\mathrm{GL}_2(\mathbb{R})$. Let $e \in (\mathbb{Z}/M)^\times$ have image mod $M/p$ inverse to $p$, let $\sigma \in \Gamma_0(M)$ have lower-right entry reducing mod $M$ to the unit $e$, and let $W_Q \in \mathrm{GL}_2(\mathbb{R})$ have matrix $\begin{pmatrix}0 & -1\\ M/p & 0\end{pmatrix}$. Then for every modular form $F$ of weight $k \in \mathbb{Z}$ on $\Gamma_H(M)$ there is a modular form $F'$ of weight $k$ on $\Gamma_H(M)$ whose underlying function is $F \mid_k (\sigma \cdot \mathtt{Wd.alGL})$ and which satisfies $\mathrm{Tr}(F)\mid_k W_Q = \mathrm{Tr}(F')$ as functions on the upper half-plane, where $\mathrm{Tr}$ denotes `ModularForm.trace` from $\Gamma_H(M)$ to $\Gamma_{H'}(M/p)$.
--
--   This is the classical compatibility of the trace (level-lowering) operator from level $M = pQ$ to level $Q$ with the Atkin–Lehner involution $w_Q$ at level $M$, corrected by the diamond operator attached to $e$, and the Fricke involution at level $Q$. It is used in the computation of $q$-expansions of traces of forms at the cusp $W_Q(\infty)$, in [`CuspForm.exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet`](thm.html#CuspForm.exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace
    (p M : ℕ) [NeZero p] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    [((CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))).IsFiniteRelIndex
      (CohCarrier.GammaH (M / p) (H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))) : Subgroup (GL (Fin 2) ℝ))]
    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ)
    (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 M) (hσe : CohCarrier.gamma0Units M ⟨σ, hσ⟩ = e)
    (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((M / p : ℕ) : ℝ), 0])
    {k : ℤ} (F : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ F' : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑F' : UpperHalfPlane → ℂ) =
        (⇑F : UpperHalfPlane → ℂ) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * Wd.alGL) ∧
      (⇑(ModularForm.trace
          (CohCarrier.GammaH (M / p) (H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))) : Subgroup (GL (Fin 2) ℝ)) F) :
          UpperHalfPlane → ℂ) ∣[k] WQ =
        ⇑(ModularForm.trace
          (CohCarrier.GammaH (M / p) (H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))) : Subgroup (GL (Fin 2) ℝ)) F') := by sorry
