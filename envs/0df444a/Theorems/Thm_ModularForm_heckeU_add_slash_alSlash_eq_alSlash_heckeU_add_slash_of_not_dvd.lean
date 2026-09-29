-- Prove2me | Theorems.Thm_ModularForm_heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd
-- name    : ModularForm.heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/e2986d79-1f2a-5abe-9fd4-d3a51ff15d79
-- title:
--   Atkin–Lehner twist of T_ℓ on Γ_H(M)-invariant functions
-- statement:
--   Let $M \ge 1$ and let $p$ be a prime with $p \mid M$ and $p^2 \nmid M$, so that $Q := M/p$ divides $M$. Let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit $u$ whose image under the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/Q)^\times$ is trivial, and let $W$ be an Atkin–Lehner datum for the pair $(M, Q)$: an integer $R$ with $M = QR$ together with $a, b \in \mathbb{Z}$ satisfying $Qa - Rb = 1$, giving rise to the element $W.\mathrm{alGL} \in \mathrm{GL}(2,\mathbb{R})$ obtained from its integral matrix. Let $\ell$ be a prime with $\ell \nmid M$ and $k \in \mathbb{Z}$. Let $\sigma \in \mathrm{SL}(2,\mathbb{Z})$ lie in $\Gamma_0(M)$ with lower-right entry $\equiv \ell \pmod M$, and let $\rho \in \mathrm{SL}(2,\mathbb{Z})$ lie in $\Gamma_0(M)$ with lower-right entry $d_\rho$ satisfying $d_\rho \ell \equiv 1 \pmod Q$. Let $f \colon \mathbb{H} \to \mathbb{C}$ satisfy $f \mid_k \gamma = f$ for every $\gamma$ in the image in $\mathrm{GL}(2,\mathbb{R})$ of $\Gamma_H(M)$, the group of elements of $\Gamma_0(M)$ whose lower-right entry, read as a unit of $\mathbb{Z}/M$, lies in $H$. Writing $U_\ell g := \sum_{j=0}^{\ell-1} g \mid_k \begin{pmatrix}1 & j \\ 0 & \ell\end{pmatrix}$ and $\mathcal{T} g := U_\ell g + g \mid_k \bigl(\sigma \cdot \mathrm{diag}(\ell,1)\bigr)$, the assertion is $$\mathcal{T}\bigl(f \mid_k W.\mathrm{alGL}\bigr) = \bigl(\mathcal{T}(f \mid_k \rho)\bigr) \mid_k W.\mathrm{alGL},$$ both sides being written out as the stated sums of weight-$k$ slash actions.
--
--   This is the Atkin–Lehner commutation law for the Hecke operator $T_\ell = U_\ell + \langle \ell \rangle\,\mathrm{diag}(\ell,1)$ at a prime $\ell$ prime to the level: conjugation by the Atkin–Lehner element at $Q = M/p$ intertwines $T_\ell$ with $T_\ell$ precomposed by the diamond operator attached to $\rho$, which represents $\ell^{-1}$ modulo $Q$ and is trivial on the $p$-part by the hypothesis on $H$. It is used in the comparison of Hecke operators under the twisting correspondence on modular curves, in [`ModularCurve.twist_correspondence_heckeT_eq_genDiffModL_T_of_atkinLehnerPinAlong`](thm.html#ModularCurve.twist_correspondence_heckeT_eq_genDiffModL_T_of_atkinLehnerPinAlong).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd.lean

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M (M / p))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (k : ℤ)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 M)
    (hσℓ : (((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) = ℓ)
    (ρ : SL(2, ℤ)) (hρ : ρ ∈ CongruenceSubgroup.Gamma0 M)
    (hρℓ : (((ρ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p)) * (ℓ : ZMod (M / p)) = 1)
    (f : UpperHalfPlane → ℂ)
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    ModularForm.heckeU k ℓ (ModularForm.alSlash W k f) +
        (ModularForm.alSlash W k f) ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ) =
      ModularForm.alSlash W k
        (ModularForm.heckeU k ℓ (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ρ : GL (Fin 2) ℝ)) +
          (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ρ : GL (Fin 2) ℝ)) ∣[k]
            ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ)) := by sorry
